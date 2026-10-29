import BstLean.Part268CellShard31Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13125_0 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (1681395378911 / 2000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (110094832271 / 5000000000000 : ℝ))
      (E := (cell13125 ⟨0, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (1681395378911 / 2000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (110094832271 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_1 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (84034880273501 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (550475169683 / 25000000000000 : ℝ))
      (E := (cell13125 ⟨1, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (84034880273501 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (550475169683 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_2 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (42000008207133 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1100952357513 / 50000000000000 : ℝ))
      (E := (cell13125 ⟨2, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (42000008207133 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1100952357513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_3 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (83965177331611 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201908704757 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨3, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (83965177331611 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201908704757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_4 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (10491295373687 / 12500000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (440382542783 / 20000000000000 : ℝ))
      (E := (cell13125 ⟨4, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (10491295373687 / 12500000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (440382542783 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_5 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (41947786676033 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1100958375183 / 50000000000000 : ℝ))
      (E := (cell13125 ⟨5, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (41947786676033 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1100958375183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_6 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (41930404191829 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201920763723 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨6, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (41930404191829 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201920763723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_7 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (83826068048793 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201924761273 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨7, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (83826068048793 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201924761273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_8 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (83791352312179 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201928750047 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨8, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (83791352312179 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201928750047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_9 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (20939165284677 / 25000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (275241599361 / 12500000000000 : ℝ))
      (E := (cell13125 ⟨9, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (20939165284677 / 25000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (275241599361 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_10 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (41860997246727 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (220193678623 / 10000000000000 : ℝ))
      (E := (cell13125 ⟨10, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (41860997246727 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (220193678623 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_11 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (3347494093667 / 4000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201940788391 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨11, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (3347494093667 / 4000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201940788391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_12 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (83652734648809 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201944807407 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨12, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (83652734648809 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201944807407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_13 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (10452267672559 / 12500000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201948790913 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨13, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (10452267672559 / 12500000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201948790913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_14 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (83583572502461 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1720275627 / 78125000000 : ℝ))
      (E := (cell13125 ⟨14, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (83583572502461 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1720275627 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_15 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (83549027980749 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201956847647 / 100000000000000 : ℝ))
      (E := (cell13125 ⟨15, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (83549027980749 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (2201956847647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_16 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (16702901556297 / 20000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (440392174601 / 20000000000000 : ℝ))
      (E := (cell13125 ⟨16, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (16702901556297 / 20000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (440392174601 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_17 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (41740005935497 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (137622805211 / 6250000000000 : ℝ))
      (E := (cell13125 ⟨17, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (41740005935497 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (137622805211 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_18 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (83445540215773 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1100984441633 / 50000000000000 : ℝ))
      (E := (cell13125 ⟨18, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (83445540215773 / 100000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (1100984441633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13125_19 : CellCertificate 13125 (437593255156481 / 5000000000000000 : ℝ) (320064077389531 / 200000000000000000 : ℝ) (20188096380913 / 625000000000000 : ℝ)
    (cell13125 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · norm_num [cell13125]
  · have h := gap_lower (n := 13125) (a := (41705546391247 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (440394575387 / 20000000000000 : ℝ))
      (E := (cell13125 ⟨19, by decide⟩).energy) (xi := (20188096380913 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13125 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13125]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13125])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13125) (a := (41705546391247 / 50000000000000 : ℝ)) (b := (156876546451 / 100000000000000 : ℝ)) (q := (440394575387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13125])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13125]

theorem cert13126_0 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (10508719347811 / 12500000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (440357030591 / 20000000000000 : ℝ))
      (E := (cell13126 ⟨0, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (10508719347811 / 12500000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (440357030591 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_1 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (84034866116727 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100894591117 / 50000000000000 : ℝ))
      (E := (cell13126 ⟨1, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (84034866116727 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100894591117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_2 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (42000001131887 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201793214543 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨2, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (42000001131887 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201793214543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_3 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (20991290796849 / 25000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (440359440067 / 20000000000000 : ℝ))
      (E := (cell13126 ⟨3, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (20991290796849 / 25000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (440359440067 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_4 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (1678606977031 / 2000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (550450301401 / 25000000000000 : ℝ))
      (E := (cell13126 ⟨4, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (1678606977031 / 2000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (550450301401 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_5 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (41947779610193 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (220180523821 / 10000000000000 : ℝ))
      (E := (cell13126 ⟨5, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (41947779610193 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (220180523821 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_6 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (83860794258237 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (220180924777 / 10000000000000 : ℝ))
      (E := (cell13126 ⟨6, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (83860794258237 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (220180924777 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_7 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (41913026964813 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (220181324157 / 10000000000000 : ℝ))
      (E := (cell13126 ⟨7, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (41913026964813 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (220181324157 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_8 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (4189566909963 / 5000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201817284679 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨8, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (4189566909963 / 5000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201817284679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_9 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (83756647032031 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100910633913 / 50000000000000 : ℝ))
      (E := (cell13126 ⟨9, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (83756647032031 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100910633913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_10 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (41860990196507 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201825313643 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨10, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (41860990196507 / 50000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201825313643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_11 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (83687338247467 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (275228664033 / 12500000000000 : ℝ))
      (E := (cell13126 ⟨11, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (83687338247467 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (275228664033 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_12 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (83652720560827 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (550458331947 / 25000000000000 : ℝ))
      (E := (cell13126 ⟨12, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (83652720560827 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (550458331947 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_13 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (83618127298711 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (275229663481 / 12500000000000 : ℝ))
      (E := (cell13126 ⟨13, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (83618127298711 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (275229663481 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_14 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (16716711685383 / 20000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201841316097 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨14, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (16716711685383 / 20000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201841316097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_15 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (20887253477853 / 25000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (275230669729 / 12500000000000 : ℝ))
      (E := (cell13126 ⟨15, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (20887253477853 / 25000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (275230669729 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_16 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (83514493718353 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (550462344971 / 25000000000000 : ℝ))
      (E := (cell13126 ⟨16, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (83514493718353 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (550462344971 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_17 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (4173999890703 / 5000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201853386997 / 100000000000000 : ℝ))
      (E := (cell13126 ⟨17, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (4173999890703 / 5000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (2201853386997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_18 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (10430690770629 / 12500000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (88074295347 / 4000000000000 : ℝ))
      (E := (cell13126 ⟨18, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (10430690770629 / 12500000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (88074295347 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13126_19 : CellCertificate 13126 (54697517753237 / 625000000000000 : ℝ) (1600198428278977 / 1000000000000000000 : ℝ) (80746092550163 / 2500000000000000 : ℝ)
    (cell13126 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · norm_num [cell13126]
  · have h := gap_lower (n := 13126) (a := (83411078737941 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100930687089 / 50000000000000 : ℝ))
      (E := (cell13126 ⟨19, by decide⟩).energy) (xi := (80746092550163 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13126 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13126]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13126])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13126) (a := (83411078737941 / 100000000000000 : ℝ)) (b := (7843222901 / 5000000000000 : ℝ)) (q := (1100930687089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13126])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13126]

theorem cert13127_0 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (84069740621587 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (220167371409 / 10000000000000 : ℝ))
      (E := (cell13127 ⟨0, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (84069740621587 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (220167371409 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_1 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (84034851962113 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201677681487 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨1, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (84034851962113 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201677681487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_2 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (1049999851443 / 1250000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201681709813 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨2, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (1049999851443 / 1250000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201681709813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_3 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (83965149045337 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201685749589 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨3, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (83965149045337 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201685749589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_4 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (41965167357881 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (220168975099 / 10000000000000 : ℝ))
      (E := (cell13127 ⟨4, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (41965167357881 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (220168975099 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_5 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (83895545090861 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201693779777 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨5, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (83895545090861 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201693779777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_6 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (8386078013497 / 10000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (440339557113 / 20000000000000 : ℝ))
      (E := (cell13127 ⟨6, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (8386078013497 / 10000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (440339557113 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_7 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (20956509953153 / 25000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100850887819 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨7, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (20956509953153 / 25000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100850887819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_8 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (83791324088493 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201705815069 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨8, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (83791324088493 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201705815069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_9 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (41878316463753 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201709794583 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨9, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (41878316463753 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201709794583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_10 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (41860983147363 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100856918407 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨10, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (41860983147363 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100856918407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_11 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (83687324155409 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100858915949 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨11, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (83687324155409 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100858915949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_12 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (41826353237497 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (220172184393 / 10000000000000 : ℝ))
      (E := (cell13127 ⟨12, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (41826353237497 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (220172184393 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_13 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (83618113219097 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100862910273 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨13, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (83618113219097 / 100000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100862910273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_14 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (20895886088379 / 25000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100864941787 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨14, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (20895886088379 / 25000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100864941787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_15 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (41774499922111 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201733863779 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨15, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (41774499922111 / 50000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201733863779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_16 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (16702895931473 / 20000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (68804308829 / 3125000000000 : ℝ))
      (E := (cell13127 ⟨16, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (16702895931473 / 20000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (68804308829 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_17 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (8347998375927 / 10000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (137608867899 / 6250000000000 : ℝ))
      (E := (cell13127 ⟨17, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (8347998375927 / 10000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (137608867899 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_18 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (16689102423287 / 20000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100872969061 / 50000000000000 : ℝ))
      (E := (cell13127 ⟨18, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (16689102423287 / 20000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (1100872969061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13127_19 : CellCertificate 13127 (13673969712731 / 156250000000000 : ℝ) (400019122049389 / 250000000000000000 : ℝ) (20184950141057 / 625000000000000 : ℝ)
    (cell13127 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · norm_num [cell13127]
  · have h := gap_lower (n := 13127) (a := (20852766173883 / 25000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201749925483 / 100000000000000 : ℝ))
      (E := (cell13127 ⟨19, by decide⟩).energy) (xi := (20184950141057 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13127 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13127]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13127])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13127) (a := (20852766173883 / 25000000000000 : ℝ)) (b := (156852371459 / 100000000000000 : ℝ)) (q := (2201749925483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13127])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13127]

theorem cert13128_0 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (84069726462847 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (550390553281 / 25000000000000 : ℝ))
      (E := (cell13128 ⟨0, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (84069726462847 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (550390553281 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_1 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (42017418904829 / 50000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100783117183 / 50000000000000 : ℝ))
      (E := (cell13128 ⟨1, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (42017418904829 / 50000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100783117183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_2 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (16799994793853 / 20000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201570258731 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨2, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (16799994793853 / 20000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201570258731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_3 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (20991283726359 / 25000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (440314858919 / 20000000000000 : ℝ))
      (E := (cell13128 ⟨3, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (20991283726359 / 25000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (440314858919 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_4 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (83930320582129 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201578292131 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨4, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (83930320582129 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201578292131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_5 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (20973882740873 / 25000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100791158549 / 50000000000000 : ℝ))
      (E := (cell13128 ⟨5, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (20973882740873 / 25000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100791158549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_6 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (41930383006929 / 50000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100793159557 / 50000000000000 : ℝ))
      (E := (cell13128 ⟨6, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (41930383006929 / 50000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100793159557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_7 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (10478253212219 / 12500000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201590305463 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨7, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (10478253212219 / 12500000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201590305463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_8 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (83791309979879 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (440318868243 / 20000000000000 : ℝ))
      (E := (cell13128 ⟨8, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (83791309979879 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (440318868243 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_9 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (83756618825133 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201598317099 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨9, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (83756618825133 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201598317099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_10 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (83721952198587 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100801177873 / 50000000000000 : ℝ))
      (E := (cell13128 ⟨10, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (83721952198587 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100801177873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_11 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (167374620131 / 200000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (550401586823 / 25000000000000 : ℝ))
      (E := (cell13128 ⟨11, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (167374620131 / 200000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (550401586823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_12 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (83652692391309 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100805177917 / 50000000000000 : ℝ))
      (E := (cell13128 ⟨12, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (83652692391309 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100805177917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_13 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (83618099141631 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201614387161 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨13, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (83618099141631 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201614387161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_14 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (83583530282263 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201618388637 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨14, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (83583530282263 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201618388637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_15 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (83548985779177 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100811211847 / 50000000000000 : ℝ))
      (E := (cell13128 ⟨15, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (83548985779177 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (1100811211847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_16 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (83514465598523 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201626439161 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨16, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (83514465598523 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201626439161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_17 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (667839757653 / 800000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201630439783 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨17, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (667839757653 / 800000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201630439783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_18 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (83445498069981 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201634430063 / 100000000000000 : ℝ))
      (E := (cell13128 ⟨18, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (83445498069981 / 100000000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (2201634430063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13128_19 : CellCertificate 13128 (43755392150053 / 500000000000000 : ℝ) (1599954566699141 / 1000000000000000000 : ℝ) (64586807652481 / 2000000000000000 : ℝ)
    (cell13128 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · norm_num [cell13128]
  · have h := gap_lower (n := 13128) (a := (2606595332977 / 3125000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (550409618139 / 25000000000000 : ℝ))
      (E := (cell13128 ⟨19, by decide⟩).energy) (xi := (64586807652481 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13128 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13128]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13128])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13128) (a := (2606595332977 / 3125000000000 : ℝ)) (b := (9802517923 / 6250000000000 : ℝ)) (q := (550409618139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13128])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13128]

theorem cert13129_0 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (16813942461253 / 20000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201450823617 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨0, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (16813942461253 / 20000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201450823617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_1 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (84034823659361 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (17611638727 / 800000000000 : ℝ))
      (E := (cell13129 ⟨1, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (84034823659361 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (17611638727 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_2 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (2624998744539 / 3125000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100729401703 / 50000000000000 : ℝ))
      (E := (cell13129 ⟨2, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (2624998744539 / 3125000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100729401703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_3 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (20991280191923 / 25000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100731417679 / 50000000000000 : ℝ))
      (E := (cell13129 ⟨3, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (20991280191923 / 25000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100731417679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_4 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (83930306450653 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (550366707257 / 25000000000000 : ℝ))
      (E := (cell13129 ⟨4, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (83930306450653 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (550366707257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_5 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (83895516838277 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100735425089 / 50000000000000 : ℝ))
      (E := (cell13129 ⟨5, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (83895516838277 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100735425089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_6 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (838607518949 / 1000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201474848423 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨6, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (838607518949 / 1000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201474848423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_7 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (20956502896261 / 25000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201478889063 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨7, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (20956502896261 / 25000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201478889063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_8 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (83791295873417 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100741460581 / 50000000000000 : ℝ))
      (E := (cell13129 ⟨8, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (83791295873417 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100741460581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_9 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (8375660472491 / 10000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201486893439 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨9, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (8375660472491 / 10000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201486893439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_10 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (83721938104599 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100745464263 / 50000000000000 : ℝ))
      (E := (cell13129 ⟨10, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (83721938104599 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100745464263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_11 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (83687295977741 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100747458279 / 50000000000000 : ℝ))
      (E := (cell13129 ⟨11, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (83687295977741 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100747458279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_12 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (83652678309773 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100749460817 / 50000000000000 : ℝ))
      (E := (cell13129 ⟨12, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (83652678309773 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100749460817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_13 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (83618085066313 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201502949541 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨13, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (83618085066313 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201502949541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_14 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (83583516213157 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (550376736911 / 25000000000000 : ℝ))
      (E := (cell13129 ⟨14, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (83583516213157 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (550376736911 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_15 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (83548971716277 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (3522417567 / 160000000000 : ℝ))
      (E := (cell13129 ⟨15, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (83548971716277 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (3522417567 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_16 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (3340578061673 / 4000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201514991563 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨16, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (3340578061673 / 4000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201514991563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_17 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (83479955656123 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (275189873619 / 12500000000000 : ℝ))
      (E := (cell13129 ⟨17, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (83479955656123 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (275189873619 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_18 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (8344548402567 / 10000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100761517159 / 50000000000000 : ℝ))
      (E := (cell13129 ⟨18, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (8344548402567 / 10000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (1100761517159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13129_19 : CellCertificate 13129 (437540814104871 / 5000000000000000 : ℝ) (319966532755897 / 200000000000000000 : ℝ) (322908878216151 / 10000000000000000 : ℝ)
    (cell13129 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · norm_num [cell13129]
  · have h := gap_lower (n := 13129) (a := (83411036617137 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201527015401 / 100000000000000 : ℝ))
      (E := (cell13129 ⟨19, by decide⟩).energy) (xi := (322908878216151 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13129 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13129]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13129])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13129) (a := (83411036617137 / 100000000000000 : ℝ)) (b := (19603525493 / 12500000000000 : ℝ)) (q := (2201527015401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13129])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13129]

theorem cert13130_0 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (84069698151843 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201339372009 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨0, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (84069698151843 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201339372009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_1 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (84034809511223 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (1100671692631 / 50000000000000 : ℝ))
      (E := (cell13130 ⟨1, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (84034809511223 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (1100671692631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_2 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (83999945683387 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201347401733 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨2, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (83999945683387 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201347401733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_3 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (10495638329013 / 12500000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201351429797 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨3, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (10495638329013 / 12500000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201351429797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_4 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (83930292321331 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201355419627 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨4, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (83930292321331 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201355419627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_5 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (83895502715217 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201359436983 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨5, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (83895502715217 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201359436983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_6 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (16772147555619 / 20000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201363489473 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨6, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (16772147555619 / 20000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201363489473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_7 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (83825997474489 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201367468421 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨7, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (83825997474489 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201367468421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_8 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (41895640884553 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201371496867 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨8, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (41895640884553 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201371496867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_9 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (41878295313419 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (5503438809 / 250000000000 : ℝ))
      (E := (cell13130 ⟨9, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (41878295313419 / 50000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (5503438809 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_10 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (83721924012761 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (440275899413 / 20000000000000 : ℝ))
      (E := (cell13130 ⟨10, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (83721924012761 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (440275899413 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_11 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (8368728189213 / 10000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (1100691769847 / 50000000000000 : ℝ))
      (E := (cell13130 ⟨11, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (8368728189213 / 10000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (1100691769847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_12 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (5228291514399 / 6250000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (137586721333 / 6250000000000 : ℝ))
      (E := (cell13130 ⟨12, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (5228291514399 / 6250000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (137586721333 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_13 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (83618070993141 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (27517394573 / 1250000000000 : ℝ))
      (E := (cell13130 ⟨13, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (83618070993141 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (27517394573 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_14 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (20895875536549 / 25000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (440279112119 / 20000000000000 : ℝ))
      (E := (cell13130 ⟨14, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (20895875536549 / 25000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (440279112119 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_15 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (83548957655523 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201399589023 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨15, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (83548957655523 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201399589023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_16 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (8351443748727 / 10000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201403597957 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨16, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (8351443748727 / 10000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201403597957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_17 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (83479941607763 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (1100703796069 / 50000000000000 : ℝ))
      (E := (cell13130 ⟨17, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (83479941607763 / 100000000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (1100703796069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_18 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (166890939967 / 200000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201411634341 / 100000000000000 : ℝ))
      (E := (cell13130 ⟨18, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (166890939967 / 200000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (2201411634341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13130_19 : CellCertificate 13130 (437527708619977 / 5000000000000000 : ℝ) (799855389717171 / 500000000000000000 : ℝ) (32288372211717 / 1000000000000000 : ℝ)
    (cell13130 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · norm_num [cell13130]
  · have h := gap_lower (n := 13130) (a := (2606594455661 / 3125000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (550353903077 / 25000000000000 : ℝ))
      (E := (cell13130 ⟨19, by decide⟩).energy) (xi := (32288372211717 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13130 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13130]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13130])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13130) (a := (2606594455661 / 3125000000000 : ℝ)) (b := (15681612299 / 10000000000000 : ℝ)) (q := (550353903077 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13130])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13130]

theorem cert13131_0 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (4203484199979 / 5000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201227974007 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨0, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (4203484199979 / 5000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201227974007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_1 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (42017397682621 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (440246408231 / 20000000000000 : ℝ))
      (E := (cell13131 ⟨1, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (42017397682621 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (440246408231 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_2 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (83999931543683 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201235995817 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨2, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (83999931543683 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201235995817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_3 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (5247818281167 / 6250000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (1100620009997 / 50000000000000 : ℝ))
      (E := (cell13131 ⟨3, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (5247818281167 / 6250000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (1100620009997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_4 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (16786055638833 / 20000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201244063929 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨4, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (16786055638833 / 20000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201244063929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_5 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (8389548859431 / 10000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (550312019379 / 25000000000000 : ℝ))
      (E := (cell13131 ⟨5, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (8389548859431 / 10000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (550312019379 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_6 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (83860723663443 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (550313017073 / 25000000000000 : ℝ))
      (E := (cell13131 ⟨6, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (83860723663443 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (550313017073 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_7 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (41912991683043 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (550314025389 / 25000000000000 : ℝ))
      (E := (cell13131 ⟨7, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (41912991683043 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (550314025389 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_8 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (83791267666947 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (1100630034167 / 50000000000000 : ℝ))
      (E := (cell13131 ⟨8, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (83791267666947 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (1100630034167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_9 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (83756576530917 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201264091461 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨9, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (83756576530917 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201264091461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_10 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (83721909923071 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (440253623891 / 20000000000000 : ℝ))
      (E := (cell13131 ⟨10, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (83721909923071 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (440253623891 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_11 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (83687267808667 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (550318039649 / 25000000000000 : ℝ))
      (E := (cell13131 ⟨11, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (83687267808667 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (550318039649 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_12 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (83652650153143 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (550319039197 / 25000000000000 : ℝ))
      (E := (cell13131 ⟨12, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (83652650153143 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (550319039197 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_13 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (16723611384423 / 20000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (1100640088953 / 50000000000000 : ℝ))
      (E := (cell13131 ⟨13, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (16723611384423 / 20000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (1100640088953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_14 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (83583488081381 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (68790130291 / 3125000000000 : ℝ))
      (E := (cell13131 ⟨14, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (83583488081381 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (68790130291 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_15 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (5221808974807 / 6250000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201288194441 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨15, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (5221808974807 / 6250000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201288194441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_16 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (83514423434859 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (55032305003 / 2500000000000 : ℝ))
      (E := (cell13131 ⟨16, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (83514423434859 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (55032305003 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_17 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (41739963780773 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201296191093 / 100000000000000 : ℝ))
      (E := (cell13131 ⟨17, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (41739963780773 / 50000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (2201296191093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_18 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (5215340996467 / 6250000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (440260046027 / 20000000000000 : ℝ))
      (E := (cell13131 ⟨18, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (5215340996467 / 6250000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (440260046027 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13131_19 : CellCertificate 13131 (875029210090819 / 10000000000000000 : ℝ) (1599588913659467 / 1000000000000000000 : ℝ) (1008933031139 / 31250000000000 : ℝ)
    (cell13131 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · norm_num [cell13131]
  · have h := gap_lower (n := 13131) (a := (83411008547307 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (550326051247 / 25000000000000 : ℝ))
      (E := (cell13131 ⟨19, by decide⟩).energy) (xi := (1008933031139 / 31250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13131 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13131]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13131])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13131) (a := (83411008547307 / 100000000000000 : ℝ)) (b := (156804043903 / 100000000000000 : ℝ)) (q := (550326051247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13131])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13131]

theorem cert13132_0 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (42034834924737 / 50000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (1100558314807 / 50000000000000 : ℝ))
      (E := (cell13132 ⟨0, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (42034834924737 / 50000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (1100558314807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_1 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (42017390610709 / 50000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (220112063493 / 10000000000000 : ℝ))
      (E := (cell13132 ⟨1, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (42017390610709 / 50000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (220112063493 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_2 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (10499989675767 / 12500000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201124643557 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨2, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (10499989675767 / 12500000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201124643557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_3 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (16793015673479 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201128663871 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨3, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (16793015673479 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201128663871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_4 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (83930264069153 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (220113270399 / 10000000000000 : ℝ))
      (E := (cell13132 ⟨4, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (83930264069153 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (220113270399 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_5 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (83895474475557 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201136713809 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨5, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (83895474475557 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201136713809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_6 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (2620647173467 / 3125000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201140700863 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨6, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (2620647173467 / 3125000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201140700863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_7 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (16765193851967 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (550286182613 / 25000000000000 : ℝ))
      (E := (cell13132 ⟨7, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (16765193851967 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (550286182613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_8 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (83791253566937 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (550287173401 / 25000000000000 : ℝ))
      (E := (cell13132 ⟨8, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (83791253566937 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (550287173401 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_9 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (10469570304643 / 12500000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (44023054263 / 2000000000000 : ℝ))
      (E := (cell13132 ⟨9, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (10469570304643 / 12500000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (44023054263 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_10 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (8372189583553 / 10000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201156737609 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨10, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (8372189583553 / 10000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201156737609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_11 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (10460906715919 / 12500000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201160773263 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨11, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (10460906715919 / 12500000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201160773263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_12 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (2614144877439 / 3125000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (440232953603 / 20000000000000 : ℝ))
      (E := (cell13132 ⟨12, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (2614144877439 / 3125000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (440232953603 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_13 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (16723608570647 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201168785739 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨13, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (16723608570647 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201168785739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_14 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (8358347401871 / 10000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201172773799 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨14, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (8358347401871 / 10000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201172773799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_15 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (16709785908089 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201176795627 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨15, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (16709785908089 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201176795627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_16 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (83514409384591 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (550295199513 / 25000000000000 : ℝ))
      (E := (cell13132 ⟨16, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (83514409384591 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (550295199513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_17 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (2608747297421 / 3125000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201184844067 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨17, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (2608747297421 / 3125000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201184844067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_18 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (16689088381117 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201188821701 / 100000000000000 : ℝ))
      (E := (cell13132 ⟨18, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (16689088381117 / 20000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (2201188821701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13132_19 : CellCertificate 13132 (875003006761461 / 10000000000000000 : ℝ) (199933383306327 / 125000000000000000 : ℝ) (322833421757103 / 10000000000000000 : ℝ)
    (cell13132 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · norm_num [cell13132]
  · have h := gap_lower (n := 13132) (a := (83410994515603 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (275149106467 / 12500000000000 : ℝ))
      (E := (cell13132 ⟨19, by decide⟩).energy) (xi := (322833421757103 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13132 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13132]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13132])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13132) (a := (83410994515603 / 100000000000000 : ℝ)) (b := (156791966683 / 100000000000000 : ℝ)) (q := (275149106467 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13132])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13132]

theorem cert13133_0 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (42034827850763 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201005280977 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨0, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (42034827850763 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201005280977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_1 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (84034767079751 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201009282337 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨1, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (84034767079751 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201009282337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_2 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (10499987908843 / 12500000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (440202657411 / 20000000000000 : ℝ))
      (E := (cell13133 ⟨2, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (10499987908843 / 12500000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (440202657411 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_3 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (1311954128723 / 1562500000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (550254325877 / 25000000000000 : ℝ))
      (E := (cell13133 ⟨3, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (1311954128723 / 1562500000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (550254325877 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_4 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (41965124973147 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201021339813 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨4, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (41965124973147 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201021339813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_5 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (83895460358957 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201025345863 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨5, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (83895460358957 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201025345863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_6 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (20965173860149 / 25000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (550257332299 / 25000000000000 : ℝ))
      (E := (cell13133 ⟨6, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (20965173860149 / 25000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (550257332299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_7 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (41912977577867 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (275129169389 / 12500000000000 : ℝ))
      (E := (cell13133 ⟨7, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (41912977577867 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (275129169389 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_8 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (41895619734539 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (88041494907 / 4000000000000 : ℝ))
      (E := (cell13133 ⟨8, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (41895619734539 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (88041494907 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_9 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (83756548345521 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (440208277733 / 20000000000000 : ℝ))
      (E := (cell13133 ⟨9, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (83756548345521 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (440208277733 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_10 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (83721881750137 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100522704807 / 50000000000000 : ℝ))
      (E := (cell13133 ⟨10, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (83721881750137 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100522704807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_11 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (10460904956023 / 12500000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (137565586481 / 6250000000000 : ℝ))
      (E := (cell13133 ⟨11, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (10460904956023 / 12500000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (137565586481 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_12 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (83652622005099 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201053433141 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨12, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (83652622005099 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201053433141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_13 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (167236057573 / 200000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (275132180937 / 12500000000000 : ℝ))
      (E := (cell13133 ⟨13, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (167236057573 / 200000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (275132180937 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_14 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (10447932494773 / 12500000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (275132679029 / 12500000000000 : ℝ))
      (E := (cell13133 ⟨14, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (10447932494773 / 12500000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (275132679029 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_15 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (41774457743061 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (440213090157 / 20000000000000 : ℝ))
      (E := (cell13133 ⟨15, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (41774457743061 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (440213090157 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_16 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (16702879067293 / 20000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201069449981 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨16, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (16702879067293 / 20000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201069449981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_17 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (41739949737769 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100536746407 / 50000000000000 : ℝ))
      (E := (cell13133 ⟨17, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (41739949737769 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (1100536746407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_18 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (41722713934919 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (440215505117 / 20000000000000 : ℝ))
      (E := (cell13133 ⟨18, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (41722713934919 / 50000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (440215505117 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13133_19 : CellCertificate 13133 (218744201812751 / 2500000000000000 : ℝ) (1599345237803547 / 1000000000000000000 : ℝ) (16140413874703 / 500000000000000 : ℝ)
    (cell13133 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · norm_num [cell13133]
  · have h := gap_lower (n := 13133) (a := (83410980486037 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201081494259 / 100000000000000 : ℝ))
      (E := (cell13133 ⟨19, by decide⟩).energy) (xi := (16140413874703 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13133 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13133]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13133])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13133) (a := (83410980486037 / 100000000000000 : ℝ)) (b := (15677989133 / 10000000000000 : ℝ)) (q := (2201081494259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13133])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13133]

theorem cert13134_0 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (10508705194467 / 12500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (68777935253 / 3125000000000 : ℝ))
      (E := (cell13134 ⟨0, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (10508705194467 / 12500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (68777935253 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_1 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (1050434411753 / 1250000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200897983377 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨1, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (1050434411753 / 1250000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200897983377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_2 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (83999889137507 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200901984211 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨2, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (83999889137507 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200901984211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_3 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (10495631263913 / 12500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100452998413 / 50000000000000 : ℝ))
      (E := (cell13134 ⟨3, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (10495631263913 / 12500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100452998413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_4 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (83930235825589 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100454985697 / 50000000000000 : ℝ))
      (E := (cell13134 ⟨4, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (83930235825589 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100454985697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_5 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (83895446244509 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200914031647 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨5, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (83895446244509 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200914031647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_6 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (209651703331 / 250000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200918011283 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨6, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (209651703331 / 250000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200918011283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_7 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (10478242631723 / 12500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (44018440671 / 2000000000000 : ℝ))
      (E := (cell13134 ⟨7, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (10478242631723 / 12500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (44018440671 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_8 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (10473903171671 / 12500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (220092604751 / 10000000000000 : ℝ))
      (E := (cell13134 ⟨8, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (10473903171671 / 12500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (220092604751 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_9 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (41878267128023 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (275116257493 / 12500000000000 : ℝ))
      (E := (cell13134 ⟨9, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (41878267128023 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (275116257493 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_10 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (83721867666891 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (440186815477 / 20000000000000 : ℝ))
      (E := (cell13134 ⟨10, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (83721867666891 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (440186815477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_11 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (41843612785581 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100469053057 / 50000000000000 : ℝ))
      (E := (cell13134 ⟨11, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (41843612785581 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100469053057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_12 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (10456575991787 / 12500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100471047017 / 50000000000000 : ℝ))
      (E := (cell13134 ⟨12, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (10456575991787 / 12500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (1100471047017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_13 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (8361801472191 / 10000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200946105021 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨13, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (8361801472191 / 10000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200946105021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_14 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (83583445899801 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (275118768077 / 12500000000000 : ℝ))
      (E := (cell13134 ⟨14, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (83583445899801 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (275118768077 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_15 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (41774450716971 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200954101713 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨15, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (41774450716971 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200954101713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_16 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (41757190645241 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200958155907 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨16, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (41757190645241 / 50000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200958155907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_17 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (16695977087149 / 20000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200962137333 / 100000000000000 : ℝ))
      (E := (cell13134 ⟨17, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (16695977087149 / 20000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (2200962137333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_18 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (10430676729529 / 12500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (275120770871 / 12500000000000 : ℝ))
      (E := (cell13134 ⟨18, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (10430676729529 / 12500000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (275120770871 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13134_19 : CellCertificate 13134 (218737652889643 / 2500000000000000 : ℝ) (1599223427714019 / 1000000000000000000 : ℝ) (322783137174371 / 10000000000000000 : ℝ)
    (cell13134 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · norm_num [cell13134]
  · have h := gap_lower (n := 13134) (a := (83410966458611 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (44019403817 / 2000000000000 : ℝ))
      (E := (cell13134 ⟨19, by decide⟩).energy) (xi := (322783137174371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13134 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13134]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13134])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13134) (a := (83410966458611 / 100000000000000 : ℝ)) (b := (39191954461 / 25000000000000 : ℝ)) (q := (44019403817 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13134])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13134]

theorem cert13135_0 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (84069627412101 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (550195657207 / 25000000000000 : ℝ))
      (E := (cell13135 ⟨0, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (84069627412101 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (550195657207 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_1 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (16806947760577 / 20000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100393311151 / 50000000000000 : ℝ))
      (E := (cell13135 ⟨1, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (16806947760577 / 20000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100393311151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_2 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (3359995000257 / 4000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (275098834641 / 12500000000000 : ℝ))
      (E := (cell13135 ⟨2, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (3359995000257 / 4000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (275098834641 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_3 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (8396503598649 / 10000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100397342953 / 50000000000000 : ℝ))
      (E := (cell13135 ⟨3, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (8396503598649 / 10000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100397342953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_4 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (20982555426759 / 25000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100399328343 / 50000000000000 : ℝ))
      (E := (cell13135 ⟨4, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (20982555426759 / 25000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100399328343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_5 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (83895432132213 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (440160542639 / 20000000000000 : ℝ))
      (E := (cell13135 ⟨5, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (83895432132213 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (440160542639 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_6 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (41930333613177 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (137550418071 / 6250000000000 : ℝ))
      (E := (cell13135 ⟨6, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (41930333613177 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (137550418071 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_7 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (83825926953983 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100405353877 / 50000000000000 : ℝ))
      (E := (cell13135 ⟨7, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (83825926953983 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100405353877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_8 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (1309237676247 / 1562500000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (68775459941 / 3125000000000 : ℝ))
      (E := (cell13135 ⟨8, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (1309237676247 / 1562500000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (68775459941 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_9 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (83756520168719 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (137551170437 / 6250000000000 : ℝ))
      (E := (cell13135 ⟨9, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (83756520168719 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (137551170437 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_10 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (83721853585793 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (550205685231 / 25000000000000 : ℝ))
      (E := (cell13135 ⟨10, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (83721853585793 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (550205685231 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_11 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (83687211496287 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (137551672887 / 6250000000000 : ℝ))
      (E := (cell13135 ⟨11, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (83687211496287 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (137551672887 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_12 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (41826296932819 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200830808831 / 100000000000000 : ℝ))
      (E := (cell13135 ⟨12, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (41826296932819 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200830808831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_13 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (10452250082433 / 12500000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200834816473 / 100000000000000 : ℝ))
      (E := (cell13135 ⟨13, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (10452250082433 / 12500000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200834816473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_14 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (41791715921781 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (220083879459 / 10000000000000 : ℝ))
      (E := (cell13135 ⟨14, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (41791715921781 / 50000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (220083879459 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_15 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (83548887383903 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100421403309 / 50000000000000 : ℝ))
      (E := (cell13135 ⟨15, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (83548887383903 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (1100421403309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_16 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (83514367246639 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200846857607 / 100000000000000 : ℝ))
      (E := (cell13135 ⟨16, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (83514367246639 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200846857607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_17 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (83479871398093 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (550212708969 / 25000000000000 : ℝ))
      (E := (cell13135 ⟨17, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (83479871398093 / 100000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (550212708969 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_18 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (20861349951191 / 25000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200854862401 / 100000000000000 : ℝ))
      (E := (cell13135 ⟨18, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (20861349951191 / 25000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200854862401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13135_19 : CellCertificate 13135 (87492441968329 / 1000000000000000 : ℝ) (12492981532639 / 7812500000000000 : ℝ) (161379000398529 / 5000000000000000 : ℝ)
    (cell13135 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · norm_num [cell13135]
  · have h := gap_lower (n := 13135) (a := (20852738108331 / 25000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200858883217 / 100000000000000 : ℝ))
      (E := (cell13135 ⟨19, by decide⟩).energy) (xi := (161379000398529 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13135 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13135]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13135])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13135) (a := (20852738108331 / 25000000000000 : ℝ)) (b := (156755746223 / 100000000000000 : ℝ)) (q := (2200858883217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13135])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13135]

theorem cert13136_0 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (84069613270623 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (1100335662659 / 50000000000000 : ℝ))
      (E := (cell13136 ⟨0, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (84069613270623 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (1100335662659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_1 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (16806944933537 / 20000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200675372737 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨1, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (16806944933537 / 20000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200675372737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_2 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (83999860877497 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (440135873161 / 20000000000000 : ℝ))
      (E := (cell13136 ⟨2, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (83999860877497 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (440135873161 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_3 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (20991255465957 / 25000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550170842687 / 25000000000000 : ℝ))
      (E := (cell13136 ⟨3, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (20991255465957 / 25000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550170842687 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_4 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (20982551897659 / 25000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200687395683 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨4, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (20982551897659 / 25000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200687395683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_5 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (20973854505517 / 25000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (440138278101 / 20000000000000 : ℝ))
      (E := (cell13136 ⟨5, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (20973854505517 / 25000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (440138278101 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_6 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (83860653122459 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (275086927593 / 12500000000000 : ℝ))
      (E := (cell13136 ⟨6, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (83860653122459 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (275086927593 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_7 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (20956478214083 / 25000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (1100349717869 / 50000000000000 : ℝ))
      (E := (cell13136 ⟨7, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (20956478214083 / 25000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (1100349717869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_8 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (16758239437679 / 20000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200703442519 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨8, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (16758239437679 / 20000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200703442519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_9 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (4187825304177 / 5000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200707447867 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨9, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (4187825304177 / 5000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200707447867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_10 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (83721839506841 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550177864579 / 25000000000000 : ℝ))
      (E := (cell13136 ⟨10, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (83721839506841 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550177864579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_11 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (83687197423557 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200715480147 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨11, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (83687197423557 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200715480147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_12 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (669220638393 / 800000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (440143903879 / 20000000000000 : ℝ))
      (E := (cell13136 ⟨12, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (669220638393 / 800000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (440143903879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_13 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (41808993299581 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (1100361761847 / 50000000000000 : ℝ))
      (E := (cell13136 ⟨13, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (41808993299581 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (1100361761847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_14 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (16716683557893 / 20000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550181874629 / 25000000000000 : ℝ))
      (E := (cell13136 ⟨14, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (16716683557893 / 20000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550181874629 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_15 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (83548873336007 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550182876823 / 25000000000000 : ℝ))
      (E := (cell13136 ⟨15, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (83548873336007 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (550182876823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_16 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (41757176602469 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200735555079 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨16, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (41757176602469 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200735555079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_17 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (83479857362581 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200739530191 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨17, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (83479857362581 / 100000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200739530191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_18 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (20861346443859 / 25000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (1100371776803 / 50000000000000 : ℝ))
      (E := (cell13136 ⟨18, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (20861346443859 / 25000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (1100371776803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13136_19 : CellCertificate 13136 (874898231624283 / 10000000000000000 : ℝ) (799489931595313 / 500000000000000000 : ℝ) (322732868361143 / 10000000000000000 : ℝ)
    (cell13136 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · norm_num [cell13136]
  · have h := gap_lower (n := 13136) (a := (41705469205087 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200747571361 / 100000000000000 : ℝ))
      (E := (cell13136 ⟨19, by decide⟩).energy) (xi := (322732868361143 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13136 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13136]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13136])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13136) (a := (41705469205087 / 50000000000000 : ℝ)) (b := (156743676469 / 100000000000000 : ℝ)) (q := (2200747571361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13136])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13136]

theorem cert13137_0 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (84069599131301 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200560075421 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨0, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (84069599131301 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200560075421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_1 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (1050433881683 / 1250000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100282030529 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨1, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (1050433881683 / 1250000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100282030529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_2 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (83999846750723 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (137535506759 / 6250000000000 : ℝ))
      (E := (cell13137 ⟨2, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (83999846750723 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (137535506759 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_3 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (2099125193583 / 2500000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (88022884371 / 4000000000000 : ℝ))
      (E := (cell13137 ⟨3, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (2099125193583 / 2500000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (88022884371 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_4 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (20982548369097 / 25000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100288065223 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨4, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (20982548369097 / 25000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100288065223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_5 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (41947701957037 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200580121551 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨5, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (41947701957037 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200580121551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_6 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (41930319510357 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200584148119 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨6, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (41930319510357 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200584148119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_7 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (8382589876083 / 10000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (220058815949 / 10000000000000 : ℝ))
      (E := (cell13137 ⟨7, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (8382589876083 / 10000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (220058815949 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_8 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (83791183099131 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200592162693 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨8, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (83791183099131 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200592162693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_9 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (20939123000127 / 25000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (68768630141 / 3125000000000 : ℝ))
      (E := (cell13137 ⟨9, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (20939123000127 / 25000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (68768630141 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_10 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (20930456357509 / 25000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100300085739 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨10, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (20930456357509 / 25000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100300085739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_11 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (20921795838243 / 25000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100302094937 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨11, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (20921795838243 / 25000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100302094937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_12 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (20913141433689 / 25000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200608225733 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨12, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (20913141433689 / 25000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200608225733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_13 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (83617972541003 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200612226689 / 100000000000000 : ℝ))
      (E := (cell13137 ⟨13, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (83617972541003 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (2200612226689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_14 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (83583403737511 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100308128197 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨14, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (83583403737511 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100308128197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_15 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (20887214822563 / 25000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (440124052389 / 20000000000000 : ℝ))
      (E := (cell13137 ⟨15, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (20887214822563 / 25000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (440124052389 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_16 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (1304911549459 / 1562500000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (275078031041 / 12500000000000 : ℝ))
      (E := (cell13137 ⟨16, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (1304911549459 / 1562500000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (275078031041 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_17 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (10434980416151 / 12500000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100314139267 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨17, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (10434980416151 / 12500000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100314139267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_18 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (83445371748247 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100316149431 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨18, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (83445371748247 / 100000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100316149431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13137_19 : CellCertificate 13137 (34994881895227 / 400000000000000 : ℝ) (799429054374143 / 500000000000000000 : ℝ) (322707739865649 / 10000000000000000 : ℝ)
    (cell13137 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · norm_num [cell13137]
  · have h := gap_lower (n := 13137) (a := (41705462194581 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100318156789 / 50000000000000 : ℝ))
      (E := (cell13137 ⟨19, by decide⟩).energy) (xi := (322707739865649 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13137 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13137]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13137])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13137) (a := (41705462194581 / 50000000000000 : ℝ)) (b := (156731608579 / 100000000000000 : ℝ)) (q := (1100318156789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13137])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13137]

theorem cert13138_0 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (42034792497067 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (440089764257 / 20000000000000 : ℝ))
      (E := (cell13138 ⟨0, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (42034792497067 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (440089764257 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_1 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (84034696403749 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100226430447 / 50000000000000 : ℝ))
      (E := (cell13138 ⟨1, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (84034696403749 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100226430447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_2 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (83999832626103 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (440091369249 / 20000000000000 : ℝ))
      (E := (cell13138 ⟨2, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (83999832626103 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (440091369249 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_3 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (20991248406241 / 25000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100230421783 / 50000000000000 : ℝ))
      (E := (cell13138 ⟨3, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (20991248406241 / 25000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100230421783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_4 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (83930179364291 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100232430487 / 50000000000000 : ℝ))
      (E := (cell13138 ⟨4, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (83930179364291 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100232430487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_5 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (8389538980823 / 10000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (550117226583 / 25000000000000 : ℝ))
      (E := (cell13138 ⟨5, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (8389538980823 / 10000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (550117226583 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_6 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (41930312460559 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100236464627 / 50000000000000 : ℝ))
      (E := (cell13138 ⟨6, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (41930312460559 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100236464627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_7 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (83825884667477 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (34382452141 / 1562500000000 : ℝ))
      (E := (cell13138 ⟨7, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (83825884667477 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (34382452141 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_8 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (41895584506007 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (550120234169 / 25000000000000 : ℝ))
      (E := (cell13138 ⟨8, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (41895584506007 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (550120234169 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_9 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (41878238959811 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (220048493499 / 10000000000000 : ℝ))
      (E := (cell13138 ⟨9, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (41878238959811 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (220048493499 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_10 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (5232613209711 / 6250000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200488938497 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨10, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (5232613209711 / 6250000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200488938497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_11 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (83687169284533 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (55012323837 / 2500000000000 : ℝ))
      (E := (cell13138 ⟨11, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (83687169284533 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (55012323837 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_12 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (8365255167253 / 10000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (88019879439 / 4000000000000 : ℝ))
      (E := (cell13138 ⟨12, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (8365255167253 / 10000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (88019879439 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_13 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (83617958484987 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200500983613 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨13, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (83617958484987 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200500983613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_14 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (83583389687699 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100252505023 / 50000000000000 : ℝ))
      (E := (cell13138 ⟨14, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (83583389687699 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100252505023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_15 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (41774422623319 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200509012373 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨15, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (41774422623319 / 50000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200509012373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_16 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (16702865025591 / 20000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200513053803 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨16, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (16702865025591 / 20000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200513053803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_17 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (3339193171919 / 4000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200517022651 / 100000000000000 : ℝ))
      (E := (cell13138 ⟨17, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (3339193171919 / 4000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (2200517022651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_18 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (16689071544639 / 20000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (275065129987 / 12500000000000 : ℝ))
      (E := (cell13138 ⟨18, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (16689071544639 / 20000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (275065129987 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13138_19 : CellCertificate 13138 (874845866951593 / 10000000000000000 : ℝ) (319747274569307 / 200000000000000000 : ℝ) (322682615309597 / 10000000000000000 : ℝ)
    (cell13138 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · norm_num [cell13138]
  · have h := gap_lower (n := 13138) (a := (83410910370287 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100262525787 / 50000000000000 : ℝ))
      (E := (cell13138 ⟨19, by decide⟩).energy) (xi := (322682615309597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13138 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13138]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13138])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13138) (a := (83410910370287 / 100000000000000 : ℝ)) (b := (78359771277 / 50000000000000 : ℝ)) (q := (1100262525787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13138])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13138]

theorem cert13139_0 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (84069570859121 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550084405191 / 25000000000000 : ℝ))
      (E := (cell13139 ⟨0, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (84069570859121 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550084405191 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_1 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (84034682275011 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200341598617 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨1, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (84034682275011 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200341598617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_2 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (16799963700727 / 20000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (220034563801 / 10000000000000 : ℝ))
      (E := (cell13139 ⟨2, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (16799963700727 / 20000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (220034563801 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_3 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (2099124487719 / 2500000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (275043703943 / 12500000000000 : ℝ))
      (E := (cell13139 ⟨3, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (2099124487719 / 2500000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (275043703943 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_4 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (10491270656793 / 12500000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100176822607 / 50000000000000 : ℝ))
      (E := (cell13139 ⟨4, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (10491270656793 / 12500000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100176822607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_5 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (10486921963067 / 12500000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200357686879 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨5, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (10486921963067 / 12500000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200357686879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_6 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (83860610823671 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200361648163 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨6, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (83860610823671 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200361648163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_7 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (83825870576271 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (275045713791 / 12500000000000 : ℝ))
      (E := (cell13139 ⟨7, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (83825870576271 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (275045713791 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_8 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (20947788731761 / 25000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550092426607 / 25000000000000 : ℝ))
      (E := (cell13139 ⟨8, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (20947788731761 / 25000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550092426607 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_9 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (41878231920441 / 50000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200373701237 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨9, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (41878231920441 / 50000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200373701237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_10 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (83721797282861 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100188850643 / 50000000000000 : ℝ))
      (E := (cell13139 ⟨10, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (83721797282861 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100188850643 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_11 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (83687155218237 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100190856429 / 50000000000000 : ℝ))
      (E := (cell13139 ⟨11, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (83687155218237 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (1100190856429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_12 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (2614141800389 / 3125000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200385741989 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨12, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (2614141800389 / 3125000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200385741989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_13 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (83617944431113 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (220038973631 / 10000000000000 : ℝ))
      (E := (cell13139 ⟨13, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (83617944431113 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (220038973631 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_14 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (83583375640027 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200393759473 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨14, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (83583375640027 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200393759473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_15 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (20887207801291 / 25000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200397816779 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨15, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (20887207801291 / 25000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200397816779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_16 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (41757155546337 / 50000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550100449207 / 25000000000000 : ℝ))
      (E := (cell13139 ⟨16, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (41757155546337 / 50000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550100449207 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_17 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (1043497690861 / 1250000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550101455199 / 25000000000000 : ℝ))
      (E := (cell13139 ⟨17, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (1043497690861 / 1250000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (550101455199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_18 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (83445343700281 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200409834981 / 100000000000000 : ℝ))
      (E := (cell13139 ⟨18, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (83445343700281 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (2200409834981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13139_19 : CellCertificate 13139 (874819690336161 / 10000000000000000 : ℝ) (799307327740569 / 500000000000000000 : ℝ) (322657494692011 / 10000000000000000 : ℝ)
    (cell13139 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · norm_num [cell13139]
  · have h := gap_lower (n := 13139) (a := (83410896353549 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (440082768729 / 20000000000000 : ℝ))
      (E := (cell13139 ⟨19, by decide⟩).energy) (xi := (322657494692011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13139 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13139]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13139])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13139) (a := (83410896353549 / 100000000000000 : ℝ)) (b := (78353739197 / 50000000000000 : ℝ)) (q := (440082768729 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13139])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13139]

theorem cert13140_0 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (84069556726263 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200226416007 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨0, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (84069556726263 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200226416007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_1 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (84034668148427 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (110011519499 / 5000000000000 : ℝ))
      (E := (cell13140 ⟨1, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (84034668148427 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (110011519499 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_2 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (83999804383319 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200234425541 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨2, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (83999804383319 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200234425541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_3 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (41982482697353 / 50000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200238415291 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨3, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (41982482697353 / 50000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200238415291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_4 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (20982537786637 / 25000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200242425221 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨4, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (20982537786637 / 25000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200242425221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_5 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (5243460100187 / 6250000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100123231597 / 50000000000000 : ℝ))
      (E := (cell13140 ⟨5, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (5243460100187 / 6250000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100123231597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_6 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (83860596728373 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100125239413 / 50000000000000 : ℝ))
      (E := (cell13140 ⟨6, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (83860596728373 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100125239413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_7 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (83825856487213 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200254479401 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨7, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (83825856487213 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200254479401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_8 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (83791140844221 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200258471951 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨8, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (83791140844221 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200258471951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_9 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (1308694527567 / 1562500000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200262521319 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨9, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (1308694527567 / 1562500000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200262521319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_10 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (8372178321249 / 10000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (440053303587 / 20000000000000 : ℝ))
      (E := (cell13140 ⟨10, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (8372178321249 / 10000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (440053303587 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_11 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (16737428230817 / 20000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (55006763153 / 2500000000000 : ℝ))
      (E := (cell13140 ⟨11, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (16737428230817 / 20000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (55006763153 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_12 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (83652523554509 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200274551911 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨12, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (83652523554509 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200274551911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_13 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (83617930379381 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200278542939 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨13, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (83617930379381 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200278542939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_14 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (83583361594497 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (275035320357 / 12500000000000 : ℝ))
      (E := (cell13140 ⟨14, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (83583361594497 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (275035320357 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_15 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (83548817165831 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100143279379 / 50000000000000 : ℝ))
      (E := (cell13140 ⟨15, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (83548817165831 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100143279379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_16 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (83514297059531 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200290593859 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨16, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (83514297059531 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200290593859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_17 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (41739900620961 / 50000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200294614721 / 100000000000000 : ℝ))
      (E := (cell13140 ⟨17, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (41739900620961 / 50000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (2200294614721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_18 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (5215333104969 / 6250000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100149312923 / 50000000000000 : ℝ))
      (E := (cell13140 ⟨18, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (5215333104969 / 6250000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (1100149312923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13140_19 : CellCertificate 13140 (174958703506701 / 2000000000000000 : ℝ) (799246478323931 / 500000000000000000 : ℝ) (64526475602383 / 2000000000000000 : ℝ)
    (cell13140 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · norm_num [cell13140]
  · have h := gap_lower (n := 13140) (a := (83410882338947 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (275037828937 / 12500000000000 : ℝ))
      (E := (cell13140 ⟨19, by decide⟩).energy) (xi := (64526475602383 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13140 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13140]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13140])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13140) (a := (83410882338947 / 100000000000000 : ℝ)) (b := (156695416097 / 100000000000000 : ℝ)) (q := (275037828937 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13140])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13140]

theorem cert13141_0 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (42034771297779 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (275014400877 / 12500000000000 : ℝ))
      (E := (cell13141 ⟨0, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (42034771297779 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (275014400877 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_1 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (16806930804799 / 20000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100059617493 / 50000000000000 : ℝ))
      (E := (cell13141 ⟨1, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (16806930804799 / 20000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100059617493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_2 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (16799958053031 / 20000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200123208839 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨2, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (16799958053031 / 20000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200123208839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_3 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (20991237820701 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200127252727 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨3, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (20991237820701 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200127252727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_4 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (41965068520451 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200131258943 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨4, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (41965068520451 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200131258943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_5 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (83895347503597 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (34377113957 / 1562500000000 : ℝ))
      (E := (cell13141 ⟨5, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (83895347503597 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (34377113957 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_6 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (41930291317611 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200139305261 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨6, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (41930291317611 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200139305261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_7 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (41912921200151 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100071651131 / 50000000000000 : ℝ))
      (E := (cell13141 ⟨7, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (41912921200151 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100071651131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_8 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (10473890845443 / 12500000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (440029458257 / 20000000000000 : ℝ))
      (E := (cell13141 ⟨8, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (10473890845443 / 12500000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (440029458257 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_9 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (83756435689839 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100075668587 / 50000000000000 : ℝ))
      (E := (cell13141 ⟨9, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (83756435689839 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (1100075668587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_10 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (10465221143033 / 12500000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200155330357 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨10, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (10465221143033 / 12500000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200155330357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_11 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (20921781773019 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200159335157 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨11, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (20921781773019 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200159335157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_12 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (10456563687339 / 12500000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200163357609 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨12, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (10456563687339 / 12500000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200163357609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_13 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (8361791632979 / 10000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (440033469069 / 20000000000000 : ℝ))
      (E := (cell13141 ⟨13, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (8361791632979 / 10000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (440033469069 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_14 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (83583347551107 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (68755355063 / 3125000000000 : ℝ))
      (E := (cell13141 ⟨14, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (83583347551107 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (68755355063 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_15 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (20887200782159 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (550043853231 / 25000000000000 : ℝ))
      (E := (cell13141 ⟨15, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (20887200782159 / 25000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (550043853231 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_16 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (41757141514263 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200179386669 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨16, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (41757141514263 / 50000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200179386669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_17 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (83479787217103 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (275022925553 / 12500000000000 : ℝ))
      (E := (cell13141 ⟨17, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (83479787217103 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (275022925553 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_18 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (1303833057201 / 1562500000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200187412491 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨18, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (1303833057201 / 1562500000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200187412491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13141_19 : CellCertificate 13141 (874767348542753 / 10000000000000000 : ℝ) (63934851053699 / 40000000000000000 : ℝ) (80651816317083 / 2500000000000000 : ℝ)
    (cell13141 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · norm_num [cell13141]
  · have h := gap_lower (n := 13141) (a := (83410868326481 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200191473427 / 100000000000000 : ℝ))
      (E := (cell13141 ⟨19, by decide⟩).energy) (xi := (80651816317083 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13141 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13141]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13141])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13141) (a := (83410868326481 / 100000000000000 : ℝ)) (b := (156683355663 / 100000000000000 : ℝ)) (q := (2200191473427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13141])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13141]

theorem cert13142_0 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (42034764233503 / 50000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200004051641 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨0, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (42034764233503 / 50000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200004051641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_1 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (21008659975429 / 25000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200008075757 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨1, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (21008659975429 / 25000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200008075757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_2 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (41999888074571 / 50000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200012045803 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨2, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (41999888074571 / 50000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200012045803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_3 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (20991234293263 / 25000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (220001608593 / 10000000000000 : ℝ))
      (E := (cell13142 ⟨3, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (20991234293263 / 25000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (220001608593 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_4 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (41965061468703 / 50000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (137501255527 / 6250000000000 : ℝ))
      (E := (cell13142 ⟨4, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (41965061468703 / 50000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (137501255527 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_5 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (83895333406349 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200024119073 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨5, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (83895333406349 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200024119073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_6 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (83860568544219 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (440005625493 / 20000000000000 : ℝ))
      (E := (cell13142 ⟨6, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (83860568544219 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (440005625493 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_7 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (41912914157769 / 50000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200032120893 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨7, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (41912914157769 / 50000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200032120893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_8 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (20947778171253 / 25000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200036164431 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨8, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (20947778171253 / 25000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200036164431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_9 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (16751284323507 / 20000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200040148801 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨9, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (16751284323507 / 20000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200040148801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_10 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (41860877539091 / 50000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200044138553 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨10, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (41860877539091 / 50000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200044138553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_11 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (8368711303221 / 10000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100024099039 / 50000000000000 : ℝ))
      (E := (cell13142 ⟨11, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (8368711303221 / 10000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100024099039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_12 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (83652495445057 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (440010443443 / 20000000000000 : ℝ))
      (E := (cell13142 ⟨12, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (83652495445057 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (440010443443 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_13 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (83617902282341 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100028100841 / 50000000000000 : ℝ))
      (E := (cell13142 ⟨13, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (83617902282341 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100028100841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_14 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (83583333509857 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200060215133 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨14, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (83583333509857 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200060215133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_15 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (83548789093581 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100032102331 / 50000000000000 : ℝ))
      (E := (cell13142 ⟨15, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (83548789093581 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (1100032102331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_16 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (4175713449983 / 5000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200068233483 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨16, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (4175713449983 / 5000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200068233483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_17 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (4173988659721 / 5000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200072248159 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨17, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (4173988659721 / 5000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200072248159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_18 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (83445301644359 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200076253191 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨18, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (83445301644359 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200076253191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13142_19 : CellCertificate 13142 (87474118336303 / 1000000000000000 : ℝ) (799124807280373 / 500000000000000000 : ℝ) (322582156460287 / 10000000000000000 : ℝ)
    (cell13142 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · norm_num [cell13142]
  · have h := gap_lower (n := 13142) (a := (83410854316149 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200080311139 / 100000000000000 : ℝ))
      (E := (cell13142 ⟨19, by decide⟩).energy) (xi := (322582156460287 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13142 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13142]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13142])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13142) (a := (83410854316149 / 100000000000000 : ℝ)) (b := (156671297093 / 100000000000000 : ℝ)) (q := (2200080311139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13142])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13142]

theorem cert13143_0 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (84069514340607 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1099946446017 / 50000000000000 : ℝ))
      (E := (cell13143 ⟨0, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (84069514340607 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1099946446017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_1 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (21008656445397 / 25000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (274987114037 / 12500000000000 : ℝ))
      (E := (cell13143 ⟨1, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (21008656445397 / 25000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (274987114037 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_2 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (1049997025441 / 1250000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1099950468217 / 50000000000000 : ℝ))
      (E := (cell13143 ⟨2, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (1049997025441 / 1250000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1099950468217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_3 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (1679298461309 / 2000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1099952457451 / 50000000000000 : ℝ))
      (E := (cell13143 ⟨3, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (1679298461309 / 2000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1099952457451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_4 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (41965054418029 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1099954485819 / 50000000000000 : ℝ))
      (E := (cell13143 ⟨4, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (41965054418029 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1099954485819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_5 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (67116255449 / 80000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199912940667 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨5, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (67116255449 / 80000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199912940667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_6 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (83860554455363 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199916945441 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨6, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (83860554455363 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199916945441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_7 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (83825814232919 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (439984198663 / 20000000000000 : ℝ))
      (E := (cell13143 ⟨7, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (83825814232919 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (439984198663 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_8 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (670328788869 / 800000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (137495310957 / 6250000000000 : ℝ))
      (E := (cell13143 ⟨8, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (670328788869 / 800000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (137495310957 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_9 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (670051260379 / 800000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199929014267 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨9, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (670051260379 / 800000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199929014267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_10 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (41860870507121 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (549983250153 / 25000000000000 : ℝ))
      (E := (cell13143 ⟨10, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (41860870507121 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (549983250153 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_11 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (41843549487243 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (87997482271 / 4000000000000 : ℝ))
      (E := (cell13143 ⟨11, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (41843549487243 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (87997482271 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_12 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (83652481393543 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1099970536299 / 50000000000000 : ℝ))
      (E := (cell13143 ⟨12, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (83652481393543 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1099970536299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_13 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (83617888237031 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199945053799 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨13, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (83617888237031 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199945053799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_14 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (83583319470747 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199949064029 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨14, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (83583319470747 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199949064029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_15 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (10443596882583 / 12500000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199953108589 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨15, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (10443596882583 / 12500000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199953108589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_16 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (83514254972931 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199957076079 / 100000000000000 : ℝ))
      (E := (cell13143 ⟨16, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (83514254972931 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (2199957076079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_17 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (41739879586937 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1099980543837 / 50000000000000 : ℝ))
      (E := (cell13143 ⟨17, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (41739879586937 / 50000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1099980543837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_18 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (83445287629991 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1099982573973 / 50000000000000 : ℝ))
      (E := (cell13143 ⟨18, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (83445287629991 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1099982573973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13143_19 : CellCertificate 13143 (437357510996731 / 5000000000000000 : ℝ) (319625594259689 / 200000000000000000 : ℝ) (80639262896701 / 2500000000000000 : ℝ)
    (cell13143 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · norm_num [cell13143]
  · have h := gap_lower (n := 13143) (a := (83410840307953 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1099984572317 / 50000000000000 : ℝ))
      (E := (cell13143 ⟨19, by decide⟩).energy) (xi := (80639262896701 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13143 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13143]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13143])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13143) (a := (83410840307953 / 100000000000000 : ℝ)) (b := (31331848077 / 20000000000000 : ℝ)) (q := (1099984572317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13143])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13143]

theorem cert13144_0 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (84069500216361 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099890893023 / 50000000000000 : ℝ))
      (E := (cell13144 ⟨0, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (84069500216361 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099890893023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_1 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (21008652915903 / 25000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199785802479 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨1, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (21008652915903 / 25000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199785802479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_2 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (5249984245223 / 6250000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (274973720617 / 12500000000000 : ℝ))
      (E := (cell13144 ⟨2, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (5249984245223 / 6250000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (274973720617 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_3 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (83964908959997 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199793797569 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨3, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (83964908959997 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199793797569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_4 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (41965047368429 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (219979779267 / 10000000000000 : ℝ))
      (E := (cell13144 ⟨4, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (41965047368429 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (219979779267 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_5 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (41947652609149 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (549950454001 / 25000000000000 : ℝ))
      (E := (cell13144 ⟨5, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (41947652609149 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (549950454001 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_6 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (41930270184327 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199805817183 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨6, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (41930270184327 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199805817183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_7 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (41912900076223 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (219980986151 / 10000000000000 : ℝ))
      (E := (cell13144 ⟨7, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (41912900076223 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (219980986151 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_8 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (83791084534383 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099906920003 / 50000000000000 : ℝ))
      (E := (cell13144 ⟨8, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (83791084534383 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099906920003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_9 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (41878196739679 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199817875509 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨9, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (41878196739679 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199817875509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_10 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (41860863476223 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (549955479133 / 25000000000000 : ℝ))
      (E := (cell13144 ⟨10, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (41860863476223 / 50000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (549955479133 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_11 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (83687084918903 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199825911251 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨11, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (83687084918903 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199825911251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_12 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (83652467344169 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199829923761 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨12, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (83652467344169 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199829923761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_13 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (83617874193861 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (549958489963 / 25000000000000 : ℝ))
      (E := (cell13144 ⟨13, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (83617874193861 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (549958489963 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_14 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (3343332217351 / 4000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099918983443 / 50000000000000 : ℝ))
      (E := (cell13144 ⟨14, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (3343332217351 / 4000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (1099918983443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_15 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (20887190257471 / 25000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199841950093 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨15, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (20887190257471 / 25000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199841950093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_16 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (83514240948339 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (549961493171 / 25000000000000 : ℝ))
      (E := (cell13144 ⟨16, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (83514240948339 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (549961493171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_17 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (10434968144433 / 12500000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199849981223 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨17, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (10434968144433 / 12500000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199849981223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_18 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (83445273617757 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (549963495053 / 25000000000000 : ℝ))
      (E := (cell13144 ⟨18, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (83445273617757 / 100000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (549963495053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13144_19 : CellCertificate 13144 (437344432216589 / 5000000000000000 : ℝ) (319601269310269 / 200000000000000000 : ℝ) (80632987661727 / 2500000000000000 : ℝ)
    (cell13144 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · norm_num [cell13144]
  · have h := gap_lower (n := 13144) (a := (8341082630189 / 10000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199858032211 / 100000000000000 : ℝ))
      (E := (cell13144 ⟨19, by decide⟩).energy) (xi := (80632987661727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13144 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13144]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13144])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13144) (a := (8341082630189 / 10000000000000 : ℝ)) (b := (156647185539 / 100000000000000 : ℝ)) (q := (2199858032211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13144])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13144]

theorem cert13145_0 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (42034743047133 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199670675829 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨0, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (42034743047133 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199670675829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_1 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (42017298773893 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199674688433 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨1, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (42017298773893 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199674688433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_2 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (41999866907003 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (137479919063 / 6250000000000 : ℝ))
      (E := (cell13145 ⟨2, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (41999866907003 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (137479919063 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_3 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (83964894856693 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099841338003 / 50000000000000 : ℝ))
      (E := (cell13145 ⟨3, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (83964894856693 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099841338003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_4 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (83930080639807 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199686725367 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨4, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (83930080639807 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199686725367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_5 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (41947645563747 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (549922686271 / 25000000000000 : ℝ))
      (E := (cell13145 ⟨5, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (41947645563747 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (549922686271 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_6 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (8386052628409 / 10000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099847371347 / 50000000000000 : ℝ))
      (E := (cell13145 ⟨6, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (8386052628409 / 10000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099847371347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_7 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (41912893037059 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (54992468137 / 2500000000000 : ℝ))
      (E := (cell13145 ⟨7, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (41912893037059 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (54992468137 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_8 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (16758214092457 / 20000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199702758517 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨8, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (16758214092457 / 20000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199702758517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_9 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (16751275882697 / 20000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (219970679059 / 10000000000000 : ℝ))
      (E := (cell13145 ⟨9, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (16751275882697 / 20000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (219970679059 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_10 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (83721712892791 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (439942154029 / 20000000000000 : ℝ))
      (E := (cell13145 ⟨10, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (83721712892791 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (439942154029 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_11 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (41843535432731 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (439942963923 / 20000000000000 : ℝ))
      (E := (cell13145 ⟨11, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (41843535432731 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (439942963923 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_12 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (10456556662117 / 12500000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (549929707209 / 25000000000000 : ℝ))
      (E := (cell13145 ⟨12, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (10456556662117 / 12500000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (549929707209 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_13 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (83617860152831 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (274965350441 / 12500000000000 : ℝ))
      (E := (cell13145 ⟨13, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (83617860152831 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (274965350441 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_14 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (41791645699471 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (549931716381 / 25000000000000 : ℝ))
      (E := (cell13145 ⟨14, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (41791645699471 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (549931716381 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_15 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (83548747001243 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099865422791 / 50000000000000 : ℝ))
      (E := (cell13145 ⟨15, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (83548747001243 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (1099865422791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_16 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (20878556731471 / 25000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (137483429067 / 6250000000000 : ℝ))
      (E := (cell13145 ⟨16, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (20878556731471 / 25000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (137483429067 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_17 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (83479731139189 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199738870557 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨17, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (83479731139189 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199738870557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_18 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (41722629803829 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199742924811 / 100000000000000 : ℝ))
      (E := (cell13145 ⟨18, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (41722629803829 / 50000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (2199742924811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13145_19 : CellCertificate 13145 (109332838835163 / 1250000000000000 : ℝ) (798942370157609 / 500000000000000000 : ℝ) (40313356704953 / 1250000000000000 : ℝ)
    (cell13145 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · norm_num [cell13145]
  · have h := gap_lower (n := 13145) (a := (83410812297961 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (87989876623 / 4000000000000 : ℝ))
      (E := (cell13145 ⟨19, by decide⟩).energy) (xi := (40313356704953 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13145 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13145]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13145])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13145) (a := (83410812297961 / 100000000000000 : ℝ)) (b := (78317566277 / 50000000000000 : ℝ)) (q := (87989876623 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13145])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13145]

theorem cert13146_0 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (42034735987161 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (109977978069 / 5000000000000 : ℝ))
      (E := (cell13146 ⟨0, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (42034735987161 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (109977978069 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_1 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (8403458343411 / 10000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199563570157 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨1, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (8403458343411 / 10000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199563570157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_2 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (83999719706593 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199567582951 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨2, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (83999719706593 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199567582951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_3 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (41982440377769 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (1099785804069 / 50000000000000 : ℝ))
      (E := (cell13146 ⟨3, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (41982440377769 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (1099785804069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_4 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (41965033272451 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199575653837 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨4, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (41965033272451 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199575653837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_5 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (16779055407767 / 20000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (34368431437 / 1562500000000 : ℝ))
      (E := (cell13146 ⟨5, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (16779055407767 / 20000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (34368431437 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_6 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (10482564025209 / 12500000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (1099791831989 / 50000000000000 : ℝ))
      (E := (cell13146 ⟨6, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (10482564025209 / 12500000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (1099791831989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_7 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (41912885998967 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199587643243 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨7, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (41912885998967 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199587643243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_8 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (83791056392331 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (549897918201 / 25000000000000 : ℝ))
      (E := (cell13146 ⟨8, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (83791056392331 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (549897918201 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_9 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (41878182674877 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199595701449 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨9, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (41878182674877 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199595701449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_10 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (41860849417639 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199599677623 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨10, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (41860849417639 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199599677623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_11 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (41843528407081 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199603723757 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨11, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (41843528407081 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199603723757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_12 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (83652439251843 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199607729691 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨12, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (83652439251843 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199607729691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_13 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (83617846113939 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199611759299 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨13, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (83617846113939 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199611759299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_14 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (41791638683123 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (274951969993 / 12500000000000 : ℝ))
      (E := (cell13146 ⟨14, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (41791638683123 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (274951969993 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_15 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (41774366487369 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (1099809897529 / 50000000000000 : ℝ))
      (E := (cell13146 ⟨15, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (41774366487369 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (1099809897529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_16 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (20878553226391 / 25000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199623811471 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨16, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (20878553226391 / 25000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199623811471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_17 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (1669594342501 / 2000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (549906953481 / 25000000000000 : ℝ))
      (E := (cell13146 ⟨17, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (1669594342501 / 2000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (549906953481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_18 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (83445245599693 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199631806921 / 100000000000000 : ℝ))
      (E := (cell13146 ⟨18, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (83445245599693 / 100000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (2199631806921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13146_19 : CellCertificate 13146 (874636560736967 / 10000000000000000 : ℝ) (1597763152585839 / 1000000000000000000 : ℝ) (322481760563979 / 10000000000000000 : ℝ)
    (cell13146 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · norm_num [cell13146]
  · have h := gap_lower (n := 13146) (a := (41705399148083 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (109981792651 / 5000000000000 : ℝ))
      (E := (cell13146 ⟨19, by decide⟩).energy) (xi := (322481760563979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13146 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13146]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13146])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13146) (a := (41705399148083 / 50000000000000 : ℝ)) (b := (156623081431 / 100000000000000 : ℝ)) (q := (109981792651 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13146])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13146]

theorem cert13147_0 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (84069457856529 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (439889700111 / 20000000000000 : ℝ))
      (E := (cell13147 ⟨0, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (84069457856529 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (439889700111 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_1 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (16806913864517 / 20000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (274931563191 / 12500000000000 : ℝ))
      (E := (cell13147 ⟨1, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (16806913864517 / 20000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (274931563191 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_2 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (83999705601329 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199456514567 / 100000000000000 : ℝ))
      (E := (cell13147 ⟨2, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (83999705601329 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199456514567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_3 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (8396486665653 / 10000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (439892107209 / 20000000000000 : ℝ))
      (E := (cell13147 ⟨3, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (8396486665653 / 10000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (439892107209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_4 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (16786010490429 / 20000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199464578081 / 100000000000000 : ℝ))
      (E := (cell13147 ⟨4, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (16786010490429 / 20000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199464578081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_5 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (83895262952323 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099734295283 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨5, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (83895262952323 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099734295283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_6 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (41930249060699 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (27493407263 / 1250000000000 : ℝ))
      (E := (cell13147 ⟨6, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (41930249060699 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (27493407263 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_7 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (16765151584779 / 20000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199476614799 / 100000000000000 : ℝ))
      (E := (cell13147 ⟨7, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (16765151584779 / 20000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199476614799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_8 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (83791042324519 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (219948064091 / 10000000000000 : ℝ))
      (E := (cell13147 ⟨8, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (83791042324519 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (219948064091 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_9 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (16751270257633 / 20000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199484608087 / 100000000000000 : ℝ))
      (E := (cell13147 ⟨9, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (16751270257633 / 20000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199484608087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_10 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (83721684779907 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099744319483 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨10, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (83721684779907 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099744319483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_11 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (41843521382501 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199492681791 / 100000000000000 : ℝ))
      (E := (cell13147 ⟨11, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (41843521382501 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199492681791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_12 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (83652425208889 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199496684461 / 100000000000000 : ℝ))
      (E := (cell13147 ⟨12, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (83652425208889 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199496684461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_13 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (41808916038593 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (439900130539 / 20000000000000 : ℝ))
      (E := (cell13147 ⟨13, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (41808916038593 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (439900130539 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_14 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (10447907916961 / 12500000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199504708327 / 100000000000000 : ℝ))
      (E := (cell13147 ⟨14, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (10447907916961 / 12500000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199504708327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_15 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (8354871895037 / 10000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099754341057 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨15, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (8354871895037 / 10000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099754341057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_16 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (83514198887381 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099756347713 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨16, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (83514198887381 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099756347713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_17 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (16695940622609 / 20000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199516753077 / 100000000000000 : ℝ))
      (E := (cell13147 ⟨17, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (16695940622609 / 20000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199516753077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_18 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (41722615796931 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199520743091 / 100000000000000 : ℝ))
      (E := (cell13147 ⟨18, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (41722615796931 / 50000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (2199520743091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13147_19 : CellCertificate 13147 (874610414599297 / 10000000000000000 : ℝ) (1597641583358983 / 1000000000000000000 : ℝ) (161228335709499 / 5000000000000000 : ℝ)
    (cell13147 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · norm_num [cell13147]
  · have h := gap_lower (n := 13147) (a := (83410784296503 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099762393127 / 50000000000000 : ℝ))
      (E := (cell13147 ⟨19, by decide⟩).energy) (xi := (161228335709499 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13147 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13147]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13147])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13147) (a := (83410784296503 / 100000000000000 : ℝ)) (b := (19576379021 / 12500000000000 : ℝ)) (q := (1099762393127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13147])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13147]

theorem cert13148_0 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (42034721870443 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (439867498671 / 20000000000000 : ℝ))
      (E := (cell13148 ⟨0, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (42034721870443 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (439867498671 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_1 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (10504319401651 / 12500000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199341494549 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨1, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (10504319401651 / 12500000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199341494549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_2 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (83999691498213 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (137459093741 / 6250000000000 : ℝ))
      (E := (cell13148 ⟨2, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (83999691498213 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (137459093741 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_3 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (83964852559669 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199349517649 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨3, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (83964852559669 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199349517649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_4 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (41965019180767 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (21993534981 / 1000000000000 : ℝ))
      (E := (cell13148 ⟨4, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (41965019180767 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (21993534981 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_5 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (20973812216989 / 25000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199357506971 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨5, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (20973812216989 / 25000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199357506971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_6 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (8386048404327 / 10000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199361551869 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨6, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (8386048404327 / 10000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199361551869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_7 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (83825743851999 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199365582133 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨7, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (83825743851999 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199365582133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_8 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (83791028258851 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2147821823 / 97656250000 : ℝ))
      (E := (cell13148 ⟨8, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (83791028258851 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2147821823 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_9 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (41878168614359 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199373568567 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨9, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (41878168614359 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199373568567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_10 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (20930417681669 / 25000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (219937759609 / 10000000000000 : ℝ))
      (E := (cell13148 ⟨10, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (20930417681669 / 25000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (219937759609 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_11 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (41843514358991 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (439876327121 / 20000000000000 : ℝ))
      (E := (cell13148 ⟨11, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (41843514358991 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (439876327121 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_12 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (41826205584037 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199385635013 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨12, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (41826205584037 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199385635013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_13 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (8361781804257 / 10000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (549847414547 / 25000000000000 : ℝ))
      (E := (cell13148 ⟨13, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (8361781804257 / 10000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (549847414547 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_14 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (83583249307267 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099696826247 / 50000000000000 : ℝ))
      (E := (cell13148 ⟨14, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (83583249307267 / 100000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099696826247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_15 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (41774352464069 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099698840681 / 50000000000000 : ℝ))
      (E := (cell13148 ⟨15, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (41774352464069 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099698840681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_16 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (20878546217833 / 25000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099700845811 / 50000000000000 : ℝ))
      (E := (cell13148 ⟨16, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (20878546217833 / 25000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099700845811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_17 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (41739844551587 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199405688017 / 100000000000000 : ℝ))
      (E := (cell13148 ⟨17, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (41739844551587 / 50000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (2199405688017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_18 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (20861304397541 / 25000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099704866661 / 50000000000000 : ℝ))
      (E := (cell13148 ⟨18, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (20861304397541 / 25000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (1099704866661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13148_19 : CellCertificate 13148 (43729213613371 / 500000000000000 : ℝ) (1597520032630427 / 1000000000000000000 : ℝ) (80607896550927 / 2500000000000000 : ℝ)
    (cell13148 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · norm_num [cell13148]
  · have h := gap_lower (n := 13148) (a := (20852692574743 / 25000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (549853428819 / 25000000000000 : ℝ))
      (E := (cell13148 ⟨19, by decide⟩).energy) (xi := (80607896550927 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13148 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13148]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13148])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13148) (a := (20852692574743 / 25000000000000 : ℝ)) (b := (78299492383 / 50000000000000 : ℝ)) (q := (549853428819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13148])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13148]

theorem cert13149_0 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (164198104741 / 195312500000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549806606019 / 25000000000000 : ℝ))
      (E := (cell13149 ⟨0, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (164198104741 / 195312500000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549806606019 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_1 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (84034541105981 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (137451904959 / 6250000000000 : ℝ))
      (E := (cell13149 ⟨1, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (84034541105981 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (137451904959 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_2 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (41999838698623 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199234480919 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨2, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (41999838698623 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199234480919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_3 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (20991209616239 / 25000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549809623757 / 25000000000000 : ℝ))
      (E := (cell13149 ⟨3, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (20991209616239 / 25000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549809623757 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_4 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (83930024273069 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199242471843 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨4, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (83930024273069 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199242471843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_5 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (41947617392867 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (1099623267547 / 50000000000000 : ℝ))
      (E := (cell13149 ⟨5, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (41947617392867 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (1099623267547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_6 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (16772093993457 / 20000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199250518479 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨6, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (16772093993457 / 20000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199250518479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_7 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (41912864891123 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (1099627272623 / 50000000000000 : ℝ))
      (E := (cell13149 ⟨7, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (41912864891123 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (1099627272623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_8 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (20947753548831 / 25000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199258564457 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨8, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (20947753548831 / 25000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199258564457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_9 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (20939080792853 / 25000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199262582893 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨9, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (20939080792853 / 25000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199262582893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_10 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (16744331335117 / 20000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199266548997 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨10, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (16744331335117 / 20000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199266548997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_11 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (83687014673101 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199270585203 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨11, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (83687014673101 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199270585203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_12 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (83652397129397 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199274581349 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨12, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (83652397129397 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199274581349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_13 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (20904451002523 / 25000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199278601309 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨13, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (20904451002523 / 25000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199278601309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_14 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (41791617640491 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199282650627 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨14, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (41791617640491 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199282650627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_15 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (83548690908041 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199286618193 / 100000000000000 : ℝ))
      (E := (cell13149 ⟨15, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (83548690908041 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (2199286618193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_16 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (41757085428709 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (1099645341803 / 50000000000000 : ℝ))
      (E := (cell13149 ⟨16, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (41757085428709 / 50000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (1099645341803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_17 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (83479675095437 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549823669249 / 25000000000000 : ℝ))
      (E := (cell13149 ⟨17, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (83479675095437 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549823669249 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_18 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (83445203588599 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549824665267 / 25000000000000 : ℝ))
      (E := (cell13149 ⟨18, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (83445203588599 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (549824665267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

theorem cert13149_19 : CellCertificate 13149 (174911626748093 / 2000000000000000 : ℝ) (31947970007919 / 20000000000000000 : ℝ) (20150406557321 / 625000000000000 : ℝ)
    (cell13149 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · norm_num [cell13149]
  · have h := gap_lower (n := 13149) (a := (83410756303573 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (439860539677 / 20000000000000 : ℝ))
      (E := (cell13149 ⟨19, by decide⟩).energy) (xi := (20150406557321 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13149 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13149]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13149])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13149) (a := (83410756303573 / 100000000000000 : ℝ)) (b := (156586939223 / 100000000000000 : ℝ)) (q := (439860539677 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13149])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13149]

end BstLean.Part268
