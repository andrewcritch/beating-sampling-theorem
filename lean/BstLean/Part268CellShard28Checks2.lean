import BstLean.Part268CellShard28Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13050_40 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (41347142239373 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210479823313 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨40, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (41347142239373 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210479823313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_41 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (1291568146473 / 1562500000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (276310478449 / 12500000000000 : ℝ))
      (E := (cell13050 ⟨41, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (1291568146473 / 1562500000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (276310478449 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_42 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (16525292354173 / 20000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210487796903 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨42, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (16525292354173 / 20000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210487796903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_43 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (20648146409759 / 25000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210491847671 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨43, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (20648146409759 / 25000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210491847671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_44 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (16511746589889 / 20000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (552623965199 / 25000000000000 : ℝ))
      (E := (cell13050 ⟨44, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (16511746589889 / 20000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (552623965199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_45 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (82524903672901 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105249917283 / 50000000000000 : ℝ))
      (E := (cell13050 ⟨45, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (82524903672901 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105249917283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_46 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (41245548890179 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210503884899 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨46, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (41245548890179 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210503884899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_47 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (16491463048583 / 20000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210507891909 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨47, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (16491463048583 / 20000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210507891909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_48 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (41211778015909 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (221051191221 / 10000000000000 : ℝ))
      (E := (cell13050 ⟨48, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (41211778015909 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (221051191221 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_49 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (10298727514807 / 12500000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (552628971079 / 25000000000000 : ℝ))
      (E := (cell13050 ⟨49, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (10298727514807 / 12500000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (552628971079 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_50 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (2058902686859 / 2500000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (55262998087 / 2500000000000 : ℝ))
      (E := (cell13050 ⟨50, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (2058902686859 / 2500000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (55262998087 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_51 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (16464483614241 / 20000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105261983907 / 50000000000000 : ℝ))
      (E := (cell13050 ⟨51, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (16464483614241 / 20000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105261983907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_52 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (82288751880807 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (221052795513 / 10000000000000 : ℝ))
      (E := (cell13050 ⟨52, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (82288751880807 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (221052795513 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_53 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (82255108875123 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105265970551 / 50000000000000 : ℝ))
      (E := (cell13050 ⟨53, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (82255108875123 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105265970551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_54 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (10277686128281 / 12500000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (442107196259 / 20000000000000 : ℝ))
      (E := (cell13050 ⟨54, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (10277686128281 / 12500000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (442107196259 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_55 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (82187892306419 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210540012889 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨55, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (82187892306419 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210540012889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_56 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (10269289836001 / 12500000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (552636007981 / 25000000000000 : ℝ))
      (E := (cell13050 ⟨56, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (10269289836001 / 12500000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (552636007981 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_57 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (82120768143529 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (552637008557 / 25000000000000 : ℝ))
      (E := (cell13050 ⟨57, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (82120768143529 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (552637008557 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_58 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (20521810161407 / 25000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210552015427 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨58, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (20521810161407 / 25000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210552015427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_59 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (82053736167089 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (276319503771 / 12500000000000 : ℝ))
      (E := (cell13050 ⟨59, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (82053736167089 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (276319503771 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13051_40 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (82694270402327 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (442073340549 / 20000000000000 : ℝ))
      (E := (cell13051 ⟨40, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (82694270402327 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (442073340549 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_41 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (41330173651999 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (34537042251 / 1562500000000 : ℝ))
      (E := (cell13051 ⟨41, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (41330173651999 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (34537042251 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_42 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (8262644770673 / 10000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (276296841161 / 12500000000000 : ℝ))
      (E := (cell13051 ⟨42, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (8262644770673 / 10000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (276296841161 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_43 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (16518514316207 / 20000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105189359181 / 50000000000000 : ℝ))
      (E := (cell13051 ⟨43, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (16518514316207 / 20000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105189359181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_44 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (41279359448787 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (276297841083 / 12500000000000 : ℝ))
      (E := (cell13051 ⟨44, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (41279359448787 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (276297841083 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_45 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (16504977925431 / 20000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (552596689639 / 25000000000000 : ℝ))
      (E := (cell13051 ⟨45, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (16504977925431 / 20000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (552596689639 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_46 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (82491083740731 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105195373631 / 50000000000000 : ℝ))
      (E := (cell13051 ⟨46, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (82491083740731 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105195373631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_47 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (82457301209403 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (552598687897 / 25000000000000 : ℝ))
      (E := (cell13051 ⟨47, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (82457301209403 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (552598687897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_48 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (1287867843819 / 1562500000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210398769251 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨48, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (1287867843819 / 1562500000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210398769251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_49 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (41194903048579 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105201398879 / 50000000000000 : ℝ))
      (E := (cell13051 ⟨49, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (41194903048579 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105201398879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_50 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (41178046729581 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210406834399 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨50, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (41178046729581 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210406834399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_51 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (41161202031051 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210410817219 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨51, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (41161202031051 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210410817219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_52 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (41144368938897 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210414861143 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨52, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (41144368938897 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210414861143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_53 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (16451018975639 / 20000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210418844731 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨53, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (16451018975639 / 20000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210418844731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_54 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (82221475035401 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (276302860323 / 12500000000000 : ℝ))
      (E := (cell13051 ⟨54, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (82221475035401 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (276302860323 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_55 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (82187878321647 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210426911887 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨55, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (82187878321647 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210426911887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_56 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (82154304709307 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (88417237147 / 4000000000000 : ℝ))
      (E := (cell13051 ⟨56, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (82154304709307 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (88417237147 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_57 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (82120754170893 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210434928779 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨57, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (82120754170893 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210434928779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_58 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (82087226679053 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (138152431739 / 6250000000000 : ℝ))
      (E := (cell13051 ⟨58, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (82087226679053 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (138152431739 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_59 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (82053722206571 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (442088584091 / 20000000000000 : ℝ))
      (E := (cell13051 ⟨59, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (82053722206571 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (442088584091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13052_40 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (82694256328067 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (552563409167 / 25000000000000 : ℝ))
      (E := (cell13052 ⟨40, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (82694256328067 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (552563409167 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_41 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (41330166617941 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (44205152701 / 2000000000000 : ℝ))
      (E := (cell13052 ⟨41, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (41330166617941 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (44205152701 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_42 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (82626433644753 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (276282707173 / 12500000000000 : ℝ))
      (E := (cell13052 ⟨42, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (82626433644753 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (276282707173 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_43 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (10324069690649 / 12500000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105132821807 / 50000000000000 : ℝ))
      (E := (cell13052 ⟨43, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (10324069690649 / 12500000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105132821807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_44 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (82558704847859 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210269651119 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨44, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (82558704847859 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210269651119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_45 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (82524875583563 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (110513683913 / 5000000000000 : ℝ))
      (E := (cell13052 ⟨45, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (82524875583563 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (110513683913 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_46 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (41245534851629 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (110513883213 / 5000000000000 : ℝ))
      (E := (cell13052 ⟨46, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (41245534851629 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (110513883213 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_47 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (20614321794511 / 25000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210281724871 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨47, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (20614321794511 / 25000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210281724871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_48 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (16484705595833 / 20000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210285680977 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨48, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (16484705595833 / 20000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210285680977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_49 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (20597448019503 / 25000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (442057941383 / 20000000000000 : ℝ))
      (E := (cell13052 ⟨49, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (20597448019503 / 25000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (442057941383 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_50 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (16471215889223 / 20000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (442058748207 / 20000000000000 : ℝ))
      (E := (cell13052 ⟨50, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (16471215889223 / 20000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (442058748207 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_51 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (82322390055149 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105148890209 / 50000000000000 : ℝ))
      (E := (cell13052 ⟨51, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (82322390055149 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105148890209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_52 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (8228872387693 / 10000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105150881437 / 50000000000000 : ℝ))
      (E := (cell13052 ⟨52, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (8228872387693 / 10000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105150881437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_53 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (16451016176683 / 20000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (442061160633 / 20000000000000 : ℝ))
      (E := (cell13052 ⟨53, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (16451016176683 / 20000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (442061160633 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_54 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (822214610467 / 1000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (552577444899 / 25000000000000 : ℝ))
      (E := (cell13052 ⟨54, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (822214610467 / 1000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (552577444899 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_55 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (4109393216951 / 5000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210313806607 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨55, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (4109393216951 / 5000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210313806607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_56 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (82154290732751 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (552579455287 / 25000000000000 : ℝ))
      (E := (cell13052 ⟨56, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (82154290732751 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (552579455287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_57 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (41060370100201 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (552580454763 / 25000000000000 : ℝ))
      (E := (cell13052 ⟨57, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (41060370100201 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (552580454763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_58 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (41043606357311 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105162927573 / 50000000000000 : ℝ))
      (E := (cell13052 ⟨58, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (41043606357311 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105162927573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_59 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (16410741649639 / 20000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105164932847 / 50000000000000 : ℝ))
      (E := (cell13052 ⟨59, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (16410741649639 / 20000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105164932847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13053_40 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (82694242255967 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210140566299 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨40, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (82694242255967 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210140566299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_41 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (20665079792481 / 25000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210144561747 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨41, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (20665079792481 / 25000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210144561747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_42 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (82626419584933 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (276268572649 / 12500000000000 : ℝ))
      (E := (cell13053 ⟨42, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (82626419584933 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (276268572649 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_43 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (5162033966969 / 6250000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210152564579 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨43, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (5162033966969 / 6250000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210152564579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_44 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (825586908003 / 1000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105078284643 / 50000000000000 : ℝ))
      (E := (cell13053 ⟨44, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (825586908003 / 1000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105078284643 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_45 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (41262430771063 / 50000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210160593677 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨45, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (41262430771063 / 50000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210160593677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_46 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (82491055667939 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105082317947 / 50000000000000 : ℝ))
      (E := (cell13053 ⟨46, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (82491055667939 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105082317947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_47 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (82457273148837 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105084317463 / 50000000000000 : ℝ))
      (E := (cell13053 ⟨47, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (82457273148837 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105084317463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_48 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (82423513956067 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210172647387 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨48, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (82423513956067 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210172647387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_49 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (10298722257627 / 12500000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105088335391 / 50000000000000 : ℝ))
      (E := (cell13053 ⟨49, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (10298722257627 / 12500000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105088335391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_50 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (82356065435217 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (442036140481 / 20000000000000 : ℝ))
      (E := (cell13053 ⟨50, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (82356065435217 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (442036140481 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_51 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (10290297006293 / 12500000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210184680299 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨51, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (10290297006293 / 12500000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210184680299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_52 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (82288709878213 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210188719389 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨52, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (82288709878213 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210188719389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_53 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (82255066890781 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (442038539647 / 20000000000000 : ℝ))
      (E := (cell13053 ⟨53, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (82255066890781 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (442038539647 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_54 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (16444289412029 / 20000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105098365719 / 50000000000000 : ℝ))
      (E := (cell13053 ⟨54, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (16444289412029 / 20000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105098365719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_55 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (82187850358539 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210200756181 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨55, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (82187850358539 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210200756181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_56 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (41077138379169 / 50000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105102384251 / 50000000000000 : ℝ))
      (E := (cell13053 ⟨56, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (41077138379169 / 50000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105102384251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_57 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (41060363116027 / 50000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (221020876423 / 10000000000000 : ℝ))
      (E := (cell13053 ⟨57, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (41060363116027 / 50000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (221020876423 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_58 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (82087198752333 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105106399097 / 50000000000000 : ℝ))
      (E := (cell13053 ⟨58, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (82087198752333 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105106399097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_59 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (82053694291961 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105108403329 / 50000000000000 : ℝ))
      (E := (cell13053 ⟨59, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (82053694291961 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105108403329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13054_40 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (3307769127441 / 4000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (55250687291 / 2500000000000 : ℝ))
      (E := (cell13054 ⟨40, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (3307769127441 / 4000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (55250687291 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_41 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (661282440849 / 800000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210031542957 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨41, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (661282440849 / 800000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210031542957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_42 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (8262640552727 / 10000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1105017779769 / 50000000000000 : ℝ))
      (E := (cell13054 ⟨42, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (8262640552727 / 10000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1105017779769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_43 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (82592529419973 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210039540107 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨43, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (82592529419973 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210039540107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_44 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (16511735350979 / 20000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1105021771021 / 50000000000000 : ℝ))
      (E := (cell13054 ⟨44, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (16511735350979 / 20000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1105021771021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_45 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (82524847502843 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210047563707 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨45, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (82524847502843 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210047563707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_46 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (82491041634773 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210051603243 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨46, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (82491041634773 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210051603243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_47 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (82457259121783 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210055599641 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨47, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (82457259121783 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210055599641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_48 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (82423499935119 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1105029804757 / 50000000000000 : ℝ))
      (E := (cell13054 ⟨48, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (82423499935119 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1105029804757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_49 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (8238976404617 / 10000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (69064488449 / 3125000000000 : ℝ))
      (E := (cell13054 ⟨49, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (8238976404617 / 10000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (69064488449 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_50 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (20589012856617 / 25000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1105033829747 / 50000000000000 : ℝ))
      (E := (cell13054 ⟨50, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (20589012856617 / 25000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1105033829747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_51 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (82322362047687 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1105035817469 / 50000000000000 : ℝ))
      (E := (cell13054 ⟨51, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (82322362047687 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1105035817469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_52 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (20572173970411 / 25000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210075671623 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨52, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (20572173970411 / 25000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210075671623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_53 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (16451010580059 / 20000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (552519926799 / 25000000000000 : ℝ))
      (E := (cell13054 ⟨53, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (16451010580059 / 20000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (552519926799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_54 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (10277679134467 / 12500000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210083679001 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨54, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (10277679134467 / 12500000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210083679001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_55 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (82187836380203 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1105043850739 / 50000000000000 : ℝ))
      (E := (cell13054 ⟨55, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (82187836380203 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1105043850739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_56 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (8215426278607 / 10000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1105045855789 / 50000000000000 : ℝ))
      (E := (cell13054 ⟨56, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (8215426278607 / 10000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1105045855789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_57 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (10265089033231 / 12500000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (276261970539 / 12500000000000 : ℝ))
      (E := (cell13054 ⟨57, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (10265089033231 / 12500000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (276261970539 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_58 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (41043592396093 / 50000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (276262467121 / 12500000000000 : ℝ))
      (E := (cell13054 ⟨58, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (41043592396093 / 50000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (276262467121 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_59 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (82053680337867 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210103743349 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨59, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (82053680337867 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210103743349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13055_40 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (41347107059121 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209914471473 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨40, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (41347107059121 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209914471473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_41 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (41330145522241 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209918519881 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨41, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (41330145522241 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209918519881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_42 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (82626391471763 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209922533599 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨42, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (82626391471763 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209922533599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_43 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (82592515370597 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209926511349 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨43, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (82592515370597 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209926511349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_44 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (16511732542329 / 20000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209930569387 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨44, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (16511732542329 / 20000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209930569387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_45 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (41262416732857 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (552483632363 / 25000000000000 : ℝ))
      (E := (cell13055 ⟨45, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (41262416732857 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (552483632363 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_46 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (82491027603759 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (220993856631 / 10000000000000 : ℝ))
      (E := (cell13055 ⟨46, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (82491027603759 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (220993856631 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_47 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (1030715563711 / 1250000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1104971280037 / 50000000000000 : ℝ))
      (E := (cell13055 ⟨47, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (1030715563711 / 1250000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1104971280037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_48 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (41211742958161 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (6906083023 / 312500000000 : ℝ))
      (E := (cell13055 ⟨48, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (41211742958161 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (6906083023 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_49 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (41194875016737 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (276243823209 / 12500000000000 : ℝ))
      (E := (cell13055 ⟨49, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (41194875016737 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (276243823209 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_50 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (20589009354967 / 25000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (138122163269 / 6250000000000 : ℝ))
      (E := (cell13055 ⟨50, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (20589009354967 / 25000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (138122163269 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_51 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (82322348047179 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (138122415271 / 6250000000000 : ℝ))
      (E := (cell13055 ⟨51, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (82322348047179 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (138122415271 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_52 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (41144340943611 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209962678641 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨52, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (41144340943611 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209962678641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_53 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (41127519455977 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (441993330559 / 20000000000000 : ℝ))
      (E := (cell13055 ⟨53, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (41127519455977 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (441993330559 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_54 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (82221419093471 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209970681399 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨54, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (82221419093471 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209970681399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_55 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (8218782240401 / 10000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209974701633 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨55, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (8218782240401 / 10000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209974701633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_56 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (10269281101993 / 12500000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209978709537 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨56, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (10269281101993 / 12500000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209978709537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_57 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (16424139660357 / 20000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (110499135047 / 5000000000000 : ℝ))
      (E := (cell13055 ⟨57, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (16424139660357 / 20000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (110499135047 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_58 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (4104358541709 / 5000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (138124170667 / 6250000000000 : ℝ))
      (E := (cell13055 ⟨58, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (4104358541709 / 5000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (138124170667 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_59 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (41026833192957 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1104995367497 / 50000000000000 : ℝ))
      (E := (cell13055 ⟨59, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (41026833192957 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1104995367497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13056_40 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (82694200052617 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (11049007529 / 500000000000 : ℝ))
      (E := (cell13056 ⟨40, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (82694200052617 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (11049007529 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_41 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (20665069246249 / 25000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209805492519 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨41, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (20665069246249 / 25000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209805492519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_42 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (20656594354603 / 25000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209809503373 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨42, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (20656594354603 / 25000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209809503373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_43 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (5162031332711 / 6250000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (1104906768579 / 50000000000000 : ℝ))
      (E := (cell13056 ⟨43, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (5162031332711 / 6250000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (1104906768579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_44 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (82558648670549 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (88392701343 / 4000000000000 : ℝ))
      (E := (cell13056 ⟨44, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (82558648670549 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (88392701343 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_45 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (41262409715369 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (552455387453 / 25000000000000 : ℝ))
      (E := (cell13056 ⟨45, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (41262409715369 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (552455387453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_46 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (82491013574897 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (138114099001 / 6250000000000 : ℝ))
      (E := (cell13056 ⟨46, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (82491013574897 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (138114099001 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_47 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (5153576942133 / 6250000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209829575171 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨47, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (5153576942133 / 6250000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209829575171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_48 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (3296938875987 / 4000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (1104916789947 / 50000000000000 : ℝ))
      (E := (cell13056 ⟨48, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (3296938875987 / 4000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (1104916789947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_49 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (5149358501433 / 6250000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209837595689 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨49, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (5149358501433 / 6250000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209837595689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_50 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (82356023415417 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209841619849 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨50, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (82356023415417 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209841619849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_51 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (82322334048817 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (1104922824729 / 50000000000000 : ℝ))
      (E := (cell13056 ⟨51, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (82322334048817 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (1104922824729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_52 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (41144333947473 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (276231210173 / 12500000000000 : ℝ))
      (E := (cell13056 ⟨52, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (41144333947473 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (276231210173 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_53 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (41127512462879 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (441970730641 / 20000000000000 : ℝ))
      (E := (cell13056 ⟨53, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (41127512462879 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (441970730641 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_54 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (10277675639169 / 12500000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (13811610497 / 625000000000 : ℝ))
      (E := (cell13056 ⟨54, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (10277675639169 / 12500000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (13811610497 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_55 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (41093904214981 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (1104930848757 / 50000000000000 : ℝ))
      (E := (cell13056 ⟨55, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (41093904214981 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (1104930848757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_56 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (41077117423981 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (1104932851611 / 50000000000000 : ℝ))
      (E := (cell13056 ⟨56, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (41077117423981 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (1104932851611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_57 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (10265085542483 / 12500000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (276233718957 / 12500000000000 : ℝ))
      (E := (cell13056 ⟨57, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (10265085542483 / 12500000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (276233718957 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_58 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (16417431375663 / 20000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (276234215013 / 12500000000000 : ℝ))
      (E := (cell13056 ⟨58, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (16417431375663 / 20000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (276234215013 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_59 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (82053652436101 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (441975556319 / 20000000000000 : ℝ))
      (E := (cell13056 ⟨59, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (82053652436101 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (441975556319 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13057_40 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (20673546497287 / 25000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209688535841 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨40, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (20673546497287 / 25000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209688535841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_41 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (82660262927667 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (1104846259837 / 50000000000000 : ℝ))
      (E := (cell13057 ⟨41, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (82660262927667 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (1104846259837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_42 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (82626363367217 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (220969652769 / 10000000000000 : ℝ))
      (E := (cell13057 ⟨42, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (82626363367217 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (220969652769 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_43 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (82592487278309 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209700558683 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨43, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (82592487278309 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209700558683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_44 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (41279317315803 / 50000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209704552353 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨44, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (41279317315803 / 50000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209704552353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_45 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (41262402698957 / 50000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (220970856589 / 10000000000000 : ℝ))
      (E := (cell13057 ⟨45, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (41262402698957 / 50000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (220970856589 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_46 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (82490999548187 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (6905351867 / 312500000000 : ℝ))
      (E := (cell13057 ⟨46, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (82490999548187 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (6905351867 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_47 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (82457217053527 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (552429161233 / 25000000000000 : ℝ))
      (E := (cell13057 ⟨47, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (82457217053527 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (552429161233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_48 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (41211728942589 / 50000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209720647117 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨48, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (41211728942589 / 50000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209720647117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_49 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (8238972201453 / 10000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (1104862330209 / 50000000000000 : ℝ))
      (E := (cell13057 ⟨49, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (8238972201453 / 10000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (1104862330209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_50 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (82356009413113 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209728682133 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨50, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (82356009413113 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209728682133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_51 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (82322320052603 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209732650301 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨51, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (82322320052603 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209732650301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_52 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (5143040869051 / 6250000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209736679849 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨52, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (5143040869051 / 6250000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209736679849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_53 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (20563752735427 / 25000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (276217588553 / 12500000000000 : ℝ))
      (E := (cell13057 ⟨53, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (20563752735427 / 25000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (276217588553 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_54 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (5138836945961 / 6250000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209744732477 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨54, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (5138836945961 / 6250000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209744732477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_55 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (10273474307257 / 12500000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (1104874374127 / 50000000000000 : ℝ))
      (E := (cell13057 ⟨55, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (10273474307257 / 12500000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (1104874374127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_56 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (82154220882121 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209752751791 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨56, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (82154220882121 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209752751791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_57 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (82120670380083 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209756738921 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨57, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (82120670380083 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209756738921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_58 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (82087142924591 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (552440191117 / 25000000000000 : ℝ))
      (E := (cell13057 ⟨58, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (82087142924591 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (552440191117 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_59 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (82053638488427 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (22097647647 / 1000000000000 : ℝ))
      (E := (cell13057 ⟨59, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (82053638488427 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (22097647647 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13058_40 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (82694171927837 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (441915112319 / 20000000000000 : ℝ))
      (E := (cell13058 ⟨40, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (82694171927837 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (441915112319 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_41 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (82660248872493 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (44191592027 / 2000000000000 : ℝ))
      (E := (cell13058 ⟨41, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (82660248872493 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (44191592027 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_42 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (2582073416193 / 3125000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (276197950819 / 12500000000000 : ℝ))
      (E := (cell13058 ⟨42, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (2582073416193 / 3125000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (276197950819 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_43 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (82592473235397 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (276198454347 / 12500000000000 : ℝ))
      (E := (cell13058 ⟨43, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (82592473235397 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (276198454347 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_44 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (644989223397 / 781250000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (88383665029 / 4000000000000 : ℝ))
      (E := (cell13058 ⟨44, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (644989223397 / 781250000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (88383665029 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_45 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (41262395683621 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104797818293 / 50000000000000 : ℝ))
      (E := (cell13058 ⟨45, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (41262395683621 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104797818293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_46 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (20622746380907 / 25000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104799832753 / 50000000000000 : ℝ))
      (E := (cell13058 ⟨46, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (20622746380907 / 25000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104799832753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_47 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (20614300758769 / 25000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (220960365147 / 10000000000000 : ℝ))
      (E := (cell13058 ⟨47, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (20614300758769 / 25000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (220960365147 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_48 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (82423443872831 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (552401912773 / 25000000000000 : ℝ))
      (E := (cell13058 ⟨48, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (82423443872831 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (552401912773 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_49 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (2059742700207 / 2500000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (276201465109 / 12500000000000 : ℝ))
      (E := (cell13058 ⟨49, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (2059742700207 / 2500000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (276201465109 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_50 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (82355995412957 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (552403920281 / 25000000000000 : ℝ))
      (E := (cell13058 ⟨50, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (82355995412957 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (552403920281 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_51 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (16464461211707 / 20000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209619705909 / 100000000000000 : ℝ))
      (E := (cell13058 ⟨51, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (16464461211707 / 20000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209619705909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_52 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (2571519997401 / 3125000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209623733103 / 100000000000000 : ℝ))
      (E := (cell13058 ⟨52, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (2571519997401 / 3125000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209623733103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_53 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (41127498479901 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (220962775937 / 10000000000000 : ℝ))
      (E := (cell13058 ⟨53, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (41127498479901 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (220962775937 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_54 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (10277672144943 / 12500000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209631781161 / 100000000000000 : ℝ))
      (E := (cell13058 ⟨54, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (10277672144943 / 12500000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209631781161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_55 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (82187780488293 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104817897361 / 50000000000000 : ℝ))
      (E := (cell13058 ⟨55, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (82187780488293 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104817897361 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_56 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (82154206918423 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (276204974511 / 12500000000000 : ℝ))
      (E := (cell13058 ⟨56, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (82154206918423 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (276204974511 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_57 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (20530164105611 / 25000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104821890547 / 50000000000000 : ℝ))
      (E := (cell13058 ⟨57, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (20530164105611 / 25000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104821890547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_58 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (41043564486503 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (552411951141 / 25000000000000 : ℝ))
      (E := (cell13058 ⟨58, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (41043564486503 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (552411951141 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_59 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (20513406135723 / 25000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209651861989 / 100000000000000 : ℝ))
      (E := (cell13058 ⟨59, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (20513406135723 / 25000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209651861989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13059_40 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (82694157868681 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209462641847 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨40, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (82694157868681 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209462641847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_41 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (3306409392779 / 4000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104733339371 / 50000000000000 : ℝ))
      (E := (cell13059 ⟨41, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (3306409392779 / 4000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104733339371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_42 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (82626335271289 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209470681131 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨42, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (82626335271289 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209470681131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_43 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (82592459194637 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (552368676647 / 25000000000000 : ℝ))
      (E := (cell13059 ⟨43, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (82592459194637 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (552368676647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_44 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (41279303280089 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (69046209213 / 3125000000000 : ℝ))
      (E := (cell13059 ⟨44, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (41279303280089 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (69046209213 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_45 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (82524777338721 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104741351501 / 50000000000000 : ℝ))
      (E := (cell13059 ⟨45, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (82524777338721 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104741351501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_46 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (4124548575061 / 5000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209486729293 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨46, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (4124548575061 / 5000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209486729293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_47 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (3298287560751 / 4000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209490712673 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨47, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (3298287560751 / 4000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209490712673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_48 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (10302928732829 / 12500000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209494768727 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨48, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (10302928732829 / 12500000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209494768727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_49 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (41194847002089 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (276187347131 / 12500000000000 : ℝ))
      (E := (cell13059 ⟨49, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (41194847002089 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (276187347131 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_50 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (82355981414947 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209502793871 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨50, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (82355981414947 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209502793871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_51 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (82322292066613 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (55237670407 / 2500000000000 : ℝ))
      (E := (cell13059 ⟨51, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (82322292066613 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (55237670407 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_52 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (5143039120687 / 6250000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104755391041 / 50000000000000 : ℝ))
      (E := (cell13059 ⟨52, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (5143039120687 / 6250000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104755391041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_53 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (82254982980041 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209514806041 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨53, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (82254982980041 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209514806041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_54 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (1284708799779 / 1562500000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209518825571 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨54, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (1284708799779 / 1562500000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209518825571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_55 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (2568367703771 / 3125000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104761418459 / 50000000000000 : ℝ))
      (E := (cell13059 ⟨55, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (2568367703771 / 3125000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104761418459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_56 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (16430838591373 / 20000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (276190861909 / 12500000000000 : ℝ))
      (E := (cell13059 ⟨56, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (16430838591373 / 20000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (276190861909 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_57 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (16424128493389 / 20000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209530878177 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨57, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (16424128493389 / 20000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209530878177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_58 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (82087115023561 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209534899593 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨58, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (82087115023561 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209534899593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_59 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (10256701324937 / 12500000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209538895783 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨59, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (10256701324937 / 12500000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209538895783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13060_40 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (82694143811681 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (441869943563 / 20000000000000 : ℝ))
      (E := (cell13060 ⟨40, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (82694143811681 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (441869943563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_41 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (82660220768611 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209353751851 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨41, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (82660220768611 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209353751851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_42 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (82626321226557 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (552339437857 / 25000000000000 : ℝ))
      (E := (cell13060 ⟨42, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (82626321226557 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (552339437857 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_43 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (82592445156031 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104680887059 / 50000000000000 : ℝ))
      (E := (cell13060 ⟨43, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (82592445156031 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104680887059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_44 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (82558592527693 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209365818501 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨44, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (82558592527693 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209365818501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_45 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (2578898853511 / 3125000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209369824037 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨45, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (2578898853511 / 3125000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209369824037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_46 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (41245478740481 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104686923861 / 50000000000000 : ℝ))
      (E := (cell13060 ⟨46, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (41245478740481 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104686923861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_47 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (82457175004623 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (34521528571 / 1562500000000 : ℝ))
      (E := (cell13060 ⟨47, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (82457175004623 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (34521528571 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_48 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (82423415854581 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209381823117 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨48, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (82423415854581 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209381823117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_49 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (5149355000139 / 6250000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (110469294397 / 5000000000000 : ℝ))
      (E := (cell13060 ⟨49, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (5149355000139 / 6250000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (110469294397 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_50 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (20588991854771 / 25000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209389902343 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨50, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (20588991854771 / 25000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209389902343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_51 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (82322278076837 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209393863337 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨51, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (82322278076837 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209393863337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_52 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (82288611947297 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209397885851 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨52, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (82288611947297 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209397885851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_53 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (82254969002423 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209401907527 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨53, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (82254969002423 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209401907527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_54 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (82221349214309 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209405924821 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨54, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (82221349214309 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209405924821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_55 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (82187752555193 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (276176241747 / 12500000000000 : ℝ))
      (E := (cell13060 ⟨55, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (82187752555193 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (276176241747 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_56 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (10269272374681 / 12500000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104706995093 / 50000000000000 : ℝ))
      (E := (cell13060 ⟨56, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (10269272374681 / 12500000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104706995093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_57 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (41060314256793 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209417970991 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨57, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (41060314256793 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209417970991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_58 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (41043550538127 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (441884398071 / 20000000000000 : ℝ))
      (E := (cell13060 ⟨58, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (41043550538127 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (441884398071 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_59 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (82053596658237 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104712992269 / 50000000000000 : ℝ))
      (E := (cell13060 ⟨59, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (82053596658237 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104712992269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13061_40 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (82694129756837 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104618424141 / 50000000000000 : ℝ))
      (E := (cell13061 ⟨40, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (82694129756837 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104618424141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_41 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (41330103359951 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (552310219871 / 25000000000000 : ℝ))
      (E := (cell13061 ⟨41, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (41330103359951 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (552310219871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_42 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (41313153591989 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (138077804767 / 6250000000000 : ℝ))
      (E := (cell13061 ⟨42, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (41313153591989 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (138077804767 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_43 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (10324053889947 / 12500000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104624448111 / 50000000000000 : ℝ))
      (E := (cell13061 ⟨43, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (10324053889947 / 12500000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104624448111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_44 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (82558578497359 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209252879033 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨44, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (82558578497359 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209252879033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_45 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (82524749288133 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104628470397 / 50000000000000 : ℝ))
      (E := (cell13061 ⟨45, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (82524749288133 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104628470397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_46 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (82490943462853 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (552315240469 / 25000000000000 : ℝ))
      (E := (cell13061 ⟨46, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (82490943462853 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (552315240469 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_47 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (4122858049631 / 5000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209264940139 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨47, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (4122858049631 / 5000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209264940139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_48 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (41211700924339 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (220926899117 / 10000000000000 : ℝ))
      (E := (cell13061 ⟨48, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (41211700924339 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (220926899117 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_49 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (5149354125151 / 6250000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104636497279 / 50000000000000 : ℝ))
      (E := (cell13061 ⟨49, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (5149354125151 / 6250000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104636497279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_50 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (82355953425367 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209277006541 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨50, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (82355953425367 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209277006541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_51 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (16464452817841 / 20000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104640512101 / 50000000000000 : ℝ))
      (E := (cell13061 ⟨51, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (16464452817841 / 20000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104640512101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_52 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (41144298982873 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209285044411 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨52, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (41144298982873 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209285044411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_53 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (20563738756737 / 25000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104644502371 / 50000000000000 : ℝ))
      (E := (cell13061 ⟨53, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (20563738756737 / 25000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104644502371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_54 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (16444267048981 / 20000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209293019801 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨54, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (16444267048981 / 20000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209293019801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_55 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (5136733661991 / 6250000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104648542949 / 50000000000000 : ℝ))
      (E := (cell13061 ⟨55, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (5136733661991 / 6250000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104648542949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_56 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (20538541260043 / 25000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209301080831 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨56, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (20538541260043 / 25000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209301080831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_57 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (41060307281183 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209305118719 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨57, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (41060307281183 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209305118719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_58 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (41043543565543 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209309136053 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨58, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (41043543565543 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209309136053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_59 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (82053582719117 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209313128253 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨59, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (82053582719117 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209313128253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13062_40 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (82694115704147 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (552280993617 / 25000000000000 : ℝ))
      (E := (cell13062 ⟨40, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (82694115704147 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (552280993617 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_41 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (41330096336673 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209128002837 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨41, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (41330096336673 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209128002837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_42 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (82626293143551 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104565998419 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨42, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (82626293143551 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104565998419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_43 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (41296208542637 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104568007023 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨43, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (41296208542637 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104568007023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_44 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (10319820558647 / 12500000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209140053037 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨44, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (10319820558647 / 12500000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209140053037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_45 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (5157795954129 / 6250000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104572026637 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨45, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (5157795954129 / 6250000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104572026637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_46 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (41245464723447 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209148071753 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨46, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (41245464723447 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209148071753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_47 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (20614286745691 / 25000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104576053203 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨47, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (20614286745691 / 25000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104576053203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_48 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (41211693922461 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209156095979 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨48, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (41211693922461 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209156095979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_49 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (41194826002377 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209160096903 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨49, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (41194826002377 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209160096903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_50 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (16471187886759 / 20000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209164106467 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨50, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (16471187886759 / 20000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209164106467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_51 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (41161125051859 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104584060877 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨51, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (41161125051859 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104584060877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_52 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (82288583986339 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (552293034909 / 25000000000000 : ℝ))
      (E := (cell13062 ⟨52, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (82288583986339 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (552293034909 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_53 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (16450988210723 / 20000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104588078387 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨53, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (16450988210723 / 20000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104588078387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_54 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (82221321277643 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (110459008481 / 5000000000000 : ℝ))
      (E := (cell13062 ⟨54, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (82221321277643 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (110459008481 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_55 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (41093862315329 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (110459208721 / 5000000000000 : ℝ))
      (E := (cell13062 ⟨55, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (41093862315329 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (110459208721 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_56 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (16430830217007 / 20000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104594113183 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨56, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (16430830217007 / 20000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104594113183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_57 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (16424120122657 / 20000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209192202999 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨57, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (16424120122657 / 20000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209192202999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_58 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (10260884148507 / 12500000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104598109141 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨58, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (10260884148507 / 12500000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104598109141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_59 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (82053568782133 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209200267703 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨59, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (82053568782133 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209200267703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13063_40 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (20673525413403 / 25000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (1104505577577 / 50000000000000 : ℝ))
      (E := (cell13063 ⟨40, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (20673525413403 / 25000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (1104505577577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_41 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (5166261164309 / 6250000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (1104507590357 / 50000000000000 : ℝ))
      (E := (cell13063 ⟨41, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (5166261164309 / 6250000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (1104507590357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_42 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (82626279105277 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209019171953 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨42, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (82626279105277 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209019171953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_43 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (82592403053123 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (552255796611 / 25000000000000 : ℝ))
      (E := (cell13063 ⟨43, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (82592403053123 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (552255796611 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_44 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (82558550443143 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (441805444553 / 20000000000000 : ℝ))
      (E := (cell13063 ⟨44, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (82558550443143 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (441805444553 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_45 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (16504944249229 / 20000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (276128902547 / 12500000000000 : ℝ))
      (E := (cell13063 ⟨45, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (16504944249229 / 20000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (276128902547 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_46 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (82490915433083 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (552258809069 / 25000000000000 : ℝ))
      (E := (cell13063 ⟨46, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (82490915433083 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (552258809069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_47 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (82457132975057 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209039268397 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨47, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (82457132975057 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209039268397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_48 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (5151460865207 / 6250000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (441808651097 / 20000000000000 : ℝ))
      (E := (cell13063 ⟨48, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (5151460865207 / 6250000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (441808651097 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_49 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (82389638009239 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209047253967 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨49, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (82389638009239 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209047253967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_50 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (5147245340273 / 6250000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209051261137 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨50, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (5147245340273 / 6250000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209051261137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_51 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (41161118060187 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (552263833279 / 25000000000000 : ℝ))
      (E := (cell13063 ⟨51, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (41161118060187 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (552263833279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_52 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (41144285004537 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (441811857931 / 20000000000000 : ℝ))
      (E := (cell13063 ⟨52, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (41144285004537 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (441811857931 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_53 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (3290197083297 / 4000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (276132913067 / 12500000000000 : ℝ))
      (E := (cell13063 ⟨53, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (3290197083297 / 4000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (276132913067 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_54 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (41110653656261 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209067374281 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨54, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (41110653656261 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209067374281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_55 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (41093855335801 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209071376939 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨55, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (41093855335801 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209071376939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_56 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (41077068566019 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209075367633 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨56, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (41077068566019 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209075367633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_57 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (82120586666343 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (1104539700687 / 50000000000000 : ℝ))
      (E := (cell13063 ⟨57, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (82120586666343 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (1104539700687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_58 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (20521764811791 / 25000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209083414653 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨58, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (20521764811791 / 25000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209083414653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_59 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (16410710969457 / 20000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (220908740289 / 10000000000000 : ℝ))
      (E := (cell13063 ⟨59, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (16410710969457 / 20000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (220908740289 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13064_40 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (8269408760523 / 10000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208898331563 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨40, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (8269408760523 / 10000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208898331563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_41 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (16532032917339 / 20000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104451177157 / 50000000000000 : ℝ))
      (E := (cell13064 ⟨41, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (16532032917339 / 20000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104451177157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_42 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (16525253013831 / 20000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208906342791 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨42, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (16525253013831 / 20000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208906342791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_43 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (20648097255781 / 25000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (441782070913 / 20000000000000 : ℝ))
      (E := (cell13064 ⟨43, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (20648097255781 / 25000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (441782070913 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_44 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (82558536419261 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (276114298527 / 12500000000000 : ℝ))
      (E := (cell13064 ⟨44, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (82558536419261 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (276114298527 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_45 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (660197657827 / 800000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (441783676641 / 20000000000000 : ℝ))
      (E := (cell13064 ⟨45, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (660197657827 / 800000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (441783676641 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_46 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (4124545071071 / 5000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208922396527 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨46, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (4124545071071 / 5000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208922396527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_47 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (10307139871187 / 12500000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (552231606529 / 25000000000000 : ℝ))
      (E := (cell13064 ⟨47, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (10307139871187 / 12500000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (552231606529 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_48 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (82423359843849 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (276116308711 / 12500000000000 : ℝ))
      (E := (cell13064 ⟨48, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (82423359843849 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (276116308711 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_49 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (20597406003967 / 25000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104467232877 / 50000000000000 : ℝ))
      (E := (cell13064 ⟨49, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (20597406003967 / 25000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104467232877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_50 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (16471182291417 / 20000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208938470553 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨50, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (16471182291417 / 20000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208938470553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_51 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (41161111069587 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208942481169 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨51, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (41161111069587 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208942481169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_52 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (2571517376061 / 3125000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208946494469 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨52, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (2571517376061 / 3125000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208946494469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_53 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (2570466034793 / 3125000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208950507117 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨53, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (2570466034793 / 3125000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208950507117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_54 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (82221293349541 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208954515567 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨54, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (82221293349541 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208954515567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_55 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (20546924178671 / 25000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208958516061 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨55, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (20546924178671 / 25000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208958516061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_56 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (82154123181179 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104481281897 / 50000000000000 : ℝ))
      (E := (cell13064 ⟨56, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (82154123181179 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104481281897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_57 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (41060286360769 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104483297743 / 50000000000000 : ℝ))
      (E := (cell13064 ⟨57, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (41060286360769 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104483297743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_58 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (10260880663551 / 12500000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104485303381 / 50000000000000 : ℝ))
      (E := (cell13064 ⟨58, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (10260880663551 / 12500000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104485303381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_59 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (41026770457287 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104487296521 / 50000000000000 : ℝ))
      (E := (cell13064 ⟨59, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (41026770457287 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104487296521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13065_40 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (82694073559001 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (88351422499 / 4000000000000 : ℝ))
      (E := (cell13065 ⟨40, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (82694073559001 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (88351422499 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_41 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (82660150546597 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208789582443 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨41, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (82660150546597 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208789582443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_42 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (5164140689699 / 6250000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208793568181 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨42, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (5164140689699 / 6250000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208793568181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_43 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (41296187497637 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (138049848579 / 6250000000000 : ℝ))
      (E := (cell13065 ⟨43, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (41296187497637 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (138049848579 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_44 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (10319815299691 / 12500000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208801608269 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨44, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (10319815299691 / 12500000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208801608269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_45 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (82524693212753 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (1104402800329 / 50000000000000 : ℝ))
      (E := (cell13065 ⟨45, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (82524693212753 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (1104402800329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_46 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (1288920115811 / 1562500000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (552202402857 / 25000000000000 : ℝ))
      (E := (cell13065 ⟨46, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (1288920115811 / 1562500000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (552202402857 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_47 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (41228552483041 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208813638509 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨47, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (41228552483041 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208813638509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_48 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (20605836461633 / 25000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208817620649 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨48, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (20605836461633 / 25000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208817620649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_49 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (82389610024643 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208821673269 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨49, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (82389610024643 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208821673269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_50 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (41177948735973 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (22088256757 / 1000000000000 : ℝ))
      (E := (cell13065 ⟨50, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (41177948735973 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (22088256757 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_51 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (82322208160117 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (276103710499 / 12500000000000 : ℝ))
      (E := (cell13065 ⟨51, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (82322208160117 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (276103710499 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_52 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (20572135515243 / 25000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (441766739003 / 20000000000000 : ℝ))
      (E := (cell13065 ⟨52, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (20572135515243 / 25000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (441766739003 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_53 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (20563724786617 / 25000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (276104713179 / 12500000000000 : ℝ))
      (E := (cell13065 ⟨53, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (20563724786617 / 25000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (276104713179 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_54 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (82221279388701 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (441768342339 / 20000000000000 : ℝ))
      (E := (cell13065 ⟨54, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (82221279388701 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (441768342339 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_55 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (41093841379953 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (69026430287 / 3125000000000 : ℝ))
      (E := (cell13065 ⟨55, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (41093841379953 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (69026430287 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_56 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (82154109232459 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208849755689 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨56, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (82154109232459 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208849755689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_57 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (8212055877887 / 10000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (441770757067 / 20000000000000 : ℝ))
      (E := (cell13065 ⟨57, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (8212055877887 / 10000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (441770757067 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_58 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (82087031371789 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (138053612163 / 6250000000000 : ℝ))
      (E := (cell13065 ⟨58, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (82087031371789 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (138053612163 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_59 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (41026763491999 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (27610772977 / 1250000000000 : ℝ))
      (E := (cell13065 ⟨59, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (41026763491999 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (27610772977 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13066_40 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (41347029757463 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (552168197277 / 25000000000000 : ℝ))
      (E := (cell13066 ⟨40, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (41347029757463 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (552168197277 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_41 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (20665034127163 / 25000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208676806293 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨41, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (20665034127163 / 25000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208676806293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_42 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (20656559250841 / 25000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104340394647 / 50000000000000 : ℝ))
      (E := (cell13066 ⟨42, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (20656559250841 / 25000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104340394647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_43 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (3303694438783 / 4000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104342397843 / 50000000000000 : ℝ))
      (E := (cell13066 ⟨43, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (3303694438783 / 4000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104342397843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_44 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (10319813547243 / 12500000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208688824047 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨44, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (10319813547243 / 12500000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208688824047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_45 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (82524679199279 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104346406919 / 50000000000000 : ℝ))
      (E := (cell13066 ⟨45, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (82524679199279 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104346406919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_46 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (10311359175567 / 12500000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (441739364411 / 20000000000000 : ℝ))
      (E := (cell13066 ⟨46, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (10311359175567 / 12500000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (441739364411 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_47 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (16491418192963 / 20000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208700846629 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨47, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (16491418192963 / 20000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208700846629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_48 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (515145824071 / 625000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208704885279 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨48, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (515145824071 / 625000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208704885279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_49 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (82389596035561 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (552177219129 / 25000000000000 : ℝ))
      (E := (cell13066 ⟨49, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (82389596035561 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (552177219129 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_50 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (82355883488951 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208712876577 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨50, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (82355883488951 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208712876577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_51 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (82322194183203 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104358470793 / 50000000000000 : ℝ))
      (E := (cell13066 ⟨51, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (82322194183203 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104358470793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_52 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (41144264045067 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (552180237589 / 25000000000000 : ℝ))
      (E := (cell13066 ⟨52, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (41144264045067 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (552180237589 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_53 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (82254885181701 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104362479283 / 50000000000000 : ℝ))
      (E := (cell13066 ⟨53, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (82254885181701 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104362479283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_54 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (8222126543 / 10000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208728962669 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨54, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (8222126543 / 10000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208728962669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_55 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (82187668807267 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (552183239727 / 25000000000000 : ℝ))
      (E := (cell13066 ⟨55, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (82187668807267 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (552183239727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_56 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (82154095285877 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104368501239 / 50000000000000 : ℝ))
      (E := (cell13066 ⟨56, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (82154095285877 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104368501239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_57 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (4106027241917 / 5000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208741030099 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨57, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (4106027241917 / 5000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208741030099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_58 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (16417403487461 / 20000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208745037397 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨58, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (16417403487461 / 20000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208745037397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_59 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (82053513055557 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (552187254947 / 25000000000000 : ℝ))
      (E := (cell13066 ⟨59, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (82053513055557 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (552187254947 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13067_40 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (41347022736501 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104280005733 / 50000000000000 : ℝ))
      (E := (cell13067 ⟨40, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (41347022736501 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104280005733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_41 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (41330061236429 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208564025869 / 100000000000000 : ℝ))
      (E := (cell13067 ⟨41, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (41330061236429 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208564025869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_42 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (16525244594739 / 20000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104284032481 / 50000000000000 : ℝ))
      (E := (cell13067 ⟨42, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (16525244594739 / 20000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104284032481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_43 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (3303693877841 / 4000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208572068689 / 100000000000000 : ℝ))
      (E := (cell13067 ⟨43, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (3303693877841 / 4000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208572068689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_44 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (20639623590127 / 25000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208576094429 / 100000000000000 : ℝ))
      (E := (cell13067 ⟨44, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (20639623590127 / 25000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208576094429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_45 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (82524665187953 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (441716016329 / 20000000000000 : ℝ))
      (E := (cell13067 ⟨45, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (82524665187953 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (441716016329 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_46 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (16498171879863 / 20000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104292043667 / 50000000000000 : ℝ))
      (E := (cell13067 ⟨46, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (16498171879863 / 20000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104292043667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_47 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (82457076965693 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104294054713 / 50000000000000 : ℝ))
      (E := (cell13067 ⟨47, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (82457076965693 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104294054713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_48 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (82423317858333 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (55214803641 / 2500000000000 : ℝ))
      (E := (cell13067 ⟨48, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (82423317858333 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (55214803641 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_49 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (5149348878039 / 6250000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104298067243 / 50000000000000 : ℝ))
      (E := (cell13067 ⟨49, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (5149348878039 / 6250000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104298067243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_50 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (41177934754049 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (552150033051 / 25000000000000 : ℝ))
      (E := (cell13067 ⟨50, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (41177934754049 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (552150033051 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_51 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (8232218020843 / 10000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (441720838983 / 20000000000000 : ℝ))
      (E := (cell13067 ⟨51, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (8232218020843 / 10000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (441720838983 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_52 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (82288514121437 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (276076025179 / 12500000000000 : ℝ))
      (E := (cell13067 ⟨52, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (82288514121437 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (276076025179 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_53 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (41127435609537 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (552153051859 / 25000000000000 : ℝ))
      (E := (cell13067 ⟨53, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (41127435609537 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (552153051859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_54 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (41110625736719 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208616209379 / 100000000000000 : ℝ))
      (E := (cell13067 ⟨54, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (41110625736719 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208616209379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_55 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (41093827428383 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (138038762719 / 6250000000000 : ℝ))
      (E := (cell13067 ⟨55, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (41093827428383 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (138038762719 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_56 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (82154081341431 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104312122503 / 50000000000000 : ℝ))
      (E := (cell13067 ⟨56, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (82154081341431 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104312122503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_57 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (41060265449973 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (552157067651 / 25000000000000 : ℝ))
      (E := (cell13067 ⟨57, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (41060265449973 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (552157067651 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_58 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (82087003504957 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (88345291037 / 4000000000000 : ℝ))
      (E := (cell13067 ⟨58, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (82087003504957 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (88345291037 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_59 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (82053499129251 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208636315613 / 100000000000000 : ℝ))
      (E := (cell13067 ⟨59, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (82053499129251 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208636315613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13068_40 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (8269403143323 / 10000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (552111822083 / 25000000000000 : ℝ))
      (E := (cell13068 ⟨40, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (8269403143323 / 10000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (552111822083 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_41 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (16532021687843 / 20000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (276056412497 / 12500000000000 : ℝ))
      (E := (cell13068 ⟨41, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (16532021687843 / 20000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (276056412497 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_42 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (3305048357847 / 4000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (1104227668179 / 50000000000000 : ℝ))
      (E := (cell13068 ⟨42, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (3305048357847 / 4000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (1104227668179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_43 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (82592332924623 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208459337419 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨43, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (82592332924623 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208459337419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_44 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (4127924017261 / 5000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (110423168027 / 5000000000000 : ℝ))
      (E := (cell13068 ⟨44, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (4127924017261 / 5000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (110423168027 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_45 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41262325589387 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208467345183 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨45, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41262325589387 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208467345183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_46 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (82490845396239 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (276058918543 / 12500000000000 : ℝ))
      (E := (cell13068 ⟨46, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (82490845396239 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (276058918543 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_47 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (20614265742179 / 25000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (441695073591 / 20000000000000 : ℝ))
      (E := (cell13068 ⟨47, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (20614265742179 / 25000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (441695073591 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_48 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (1648466077349 / 2000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208479401733 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨48, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (1648466077349 / 2000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208479401733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_49 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (8238956806383 / 10000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (220848338819 / 10000000000000 : ℝ))
      (E := (cell13068 ⟨49, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (8238956806383 / 10000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (220848338819 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_50 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (20588963882347 / 25000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208487442581 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨50, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (20588963882347 / 25000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208487442581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_51 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (82322166235799 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (1104245721989 / 50000000000000 : ℝ))
      (E := (cell13068 ⟨51, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (82322166235799 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (1104245721989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_52 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (32143945373 / 39062500000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (441699089649 / 20000000000000 : ℝ))
      (E := (cell13068 ⟨52, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (32143945373 / 39062500000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (441699089649 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_53 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41127428629293 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208499452043 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨53, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41127428629293 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208499452043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_54 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (16444247503803 / 20000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (1104251725913 / 50000000000000 : ℝ))
      (E := (cell13068 ⟨54, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (16444247503803 / 20000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (1104251725913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_55 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (82187640908403 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208507502971 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨55, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (82187640908403 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208507502971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_56 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (82154067399123 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208511483271 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨56, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (82154067399123 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208511483271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_57 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (10265064620461 / 12500000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (69016109589 / 3125000000000 : ℝ))
      (E := (cell13068 ⟨57, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (10265064620461 / 12500000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (69016109589 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_58 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (16417397914949 / 20000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208519569397 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨58, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (16417397914949 / 20000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208519569397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_59 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41026742602539 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (138032721747 / 6250000000000 : ℝ))
      (E := (cell13068 ⟨59, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41026742602539 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (138032721747 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13069_40 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (8269401739561 / 10000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (1104167280461 / 50000000000000 : ℝ))
      (E := (cell13069 ⟨40, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (8269401739561 / 10000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (1104167280461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_41 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (41330047203861 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (220833856981 / 10000000000000 : ℝ))
      (E := (cell13069 ⟨41, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (41330047203861 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (220833856981 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_42 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (16525238984161 / 20000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208342603481 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨42, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (16525238984161 / 20000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208342603481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_43 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (82592318905371 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208346601877 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨43, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (82592318905371 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208346601877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_44 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (1031980829151 / 1250000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (110417531119 / 5000000000000 : ℝ))
      (E := (cell13069 ⟨44, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (1031980829151 / 1250000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (110417531119 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_45 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (41262318585871 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208354663349 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨45, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (41262318585871 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208354663349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_46 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (8249083139531 / 10000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208358664007 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨46, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (8249083139531 / 10000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208358664007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_47 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (20614262243471 / 25000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208362681161 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨47, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (20614262243471 / 25000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208362681161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_48 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (82423289878711 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (138022919533 / 6250000000000 : ℝ))
      (E := (cell13069 ⟨48, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (82423289878711 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (138022919533 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_49 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (82389554081179 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (110418534831 / 5000000000000 : ℝ))
      (E := (cell13069 ⟨49, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (82389554081179 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (110418534831 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_50 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (4117792077641 / 5000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (552093672419 / 25000000000000 : ℝ))
      (E := (cell13069 ⟨50, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (4117792077641 / 5000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (552093672419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_51 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (82322152265309 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208378747817 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨51, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (82322152265309 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208378747817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_52 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (82288486190463 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (69011960933 / 3125000000000 : ℝ))
      (E := (cell13069 ⟨52, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (82288486190463 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (69011960933 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_53 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (41127421650119 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (1104193375737 / 50000000000000 : ℝ))
      (E := (cell13069 ⟨53, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (41127421650119 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (1104193375737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_54 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (8222122356673 / 10000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (1104195374561 / 50000000000000 : ℝ))
      (E := (cell13069 ⟨54, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (8222122356673 / 10000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (1104195374561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_55 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (82187626962177 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208394798177 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨55, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (82187626962177 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208394798177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_56 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (82154053458951 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (1104199388217 / 50000000000000 : ℝ))
      (E := (cell13069 ⟨56, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (82154053458951 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (1104199388217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_57 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (16424100605913 / 20000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208402798013 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨57, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (16424100605913 / 20000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208402798013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_58 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (41043487823333 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208406858611 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨58, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (41043487823333 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208406858611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_59 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (512834195519 / 625000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (110420541763 / 5000000000000 : ℝ))
      (E := (cell13069 ⟨59, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (512834195519 / 625000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (110420541763 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13070_40 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (4134700168007 / 5000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208221888023 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨40, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (4134700168007 / 5000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208221888023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_41 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (82660080378379 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208225894177 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨41, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (82660080378379 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208225894177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_42 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (5164136306099 / 6250000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104114962581 / 50000000000000 : ℝ))
      (E := (cell13070 ⟨42, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (5164136306099 / 6250000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104114962581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_43 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (41296152444133 / 50000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104116960459 / 50000000000000 : ℝ))
      (E := (cell13070 ⟨43, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (41296152444133 / 50000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104116960459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_44 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (82558452321087 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104118969413 / 50000000000000 : ℝ))
      (E := (cell13070 ⟨44, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (82558452321087 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104118969413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_45 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (16504924633371 / 20000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208241977247 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨45, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (16504924633371 / 20000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208241977247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_46 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (3299632695861 / 4000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208245975403 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨46, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (3299632695861 / 4000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208245975403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_47 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (82457034981197 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (22082499901 / 1000000000000 : ℝ))
      (E := (cell13070 ⟨47, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (82457034981197 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (22082499901 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_48 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (16484655178423 / 20000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104127009529 / 50000000000000 : ℝ))
      (E := (cell13070 ⟨48, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (16484655178423 / 20000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104127009529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_49 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (8238954010067 / 10000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104129000393 / 50000000000000 : ℝ))
      (E := (cell13070 ⟨49, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (8238954010067 / 10000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104129000393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_50 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (82355827578393 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (110413102527 / 5000000000000 : ℝ))
      (E := (cell13070 ⟨50, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (82355827578393 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (110413102527 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_51 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (128628341089 / 156250000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (69008313981 / 3125000000000 : ℝ))
      (E := (cell13070 ⟨51, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (128628341089 / 156250000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (69008313981 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_52 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (41144236114093 / 50000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (441654009441 / 20000000000000 : ℝ))
      (E := (cell13070 ⟨52, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (41144236114093 / 50000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (441654009441 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_53 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (20563707336007 / 25000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208274046643 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨53, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (20563707336007 / 25000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208274046643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_54 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (82221209616583 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208278101267 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨54, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (82221209616583 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208278101267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_55 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (10273451627261 / 12500000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208282089123 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨55, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (10273451627261 / 12500000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208282089123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_56 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (16430807904183 / 20000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (138017882781 / 6250000000000 : ℝ))
      (E := (cell13070 ⟨56, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (16430807904183 / 20000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (138017882781 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_57 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (82120489097577 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104145072051 / 50000000000000 : ℝ))
      (E := (cell13070 ⟨57, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (82120489097577 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104145072051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_58 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (41043480860361 / 50000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (138018383973 / 6250000000000 : ℝ))
      (E := (cell13070 ⟨58, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (41043480860361 / 50000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (138018383973 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_59 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (41026728681567 / 50000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (110414908877 / 5000000000000 : ℝ))
      (E := (cell13070 ⟨59, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (41026728681567 / 50000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (110414908877 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13071_40 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (82693989326821 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (44162184217 / 2000000000000 : ℝ))
      (E := (cell13071 ⟨40, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (82693989326821 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (44162184217 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_41 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (16532013270237 / 20000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (1104056607137 / 50000000000000 : ℝ))
      (E := (cell13071 ⟨41, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (16532013270237 / 20000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (1104056607137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_42 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (82626166876511 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208117242573 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨42, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (82626166876511 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208117242573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_43 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (82592290873309 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208121235689 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨43, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (82592290873309 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208121235689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_44 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (82558438312241 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (552031312751 / 25000000000000 : ℝ))
      (E := (cell13071 ⟨44, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (82558438312241 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (552031312751 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_45 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (16504921832823 / 20000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208129286877 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨45, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (16504921832823 / 20000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208129286877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_46 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (16498160679977 / 20000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (552033320633 / 25000000000000 : ℝ))
      (E := (cell13071 ⟨46, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (16498160679977 / 20000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (552033320633 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_47 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (20614255247663 / 25000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (88325491791 / 4000000000000 : ℝ))
      (E := (cell13071 ⟨47, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (20614255247663 / 25000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (88325491791 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_48 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (41211630953831 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208141321323 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨48, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (41211630953831 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208141321323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_49 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (82389526122303 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (6900454249 / 312500000000 : ℝ))
      (E := (cell13071 ⟨49, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (82389526122303 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (6900454249 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_50 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (82355813606107 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (552037337031 / 25000000000000 : ℝ))
      (E := (cell13071 ⟨50, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (82355813606107 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (552037337031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_51 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (329288497323 / 400000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441630680349 / 20000000000000 : ℝ))
      (E := (cell13071 ⟨51, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (329288497323 / 400000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441630680349 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_52 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (82288458268047 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (1104078699679 / 50000000000000 : ℝ))
      (E := (cell13071 ⟨52, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (82288458268047 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (1104078699679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_53 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (20563703847489 / 25000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208161396639 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨53, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (20563703847489 / 25000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208161396639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_54 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (82221195668573 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208165449153 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨54, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (82221195668573 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208165449153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_55 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (16437519815227 / 20000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441633886989 / 20000000000000 : ℝ))
      (E := (cell13071 ⟨55, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (16437519815227 / 20000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441633886989 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_56 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (41077012792507 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208173468299 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨56, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (41077012792507 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208173468299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_57 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (82120475167723 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (1104088742967 / 50000000000000 : ℝ))
      (E := (cell13071 ⟨57, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (82120475167723 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (1104088742967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_58 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (82086947796911 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208181483473 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨58, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (82086947796911 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208181483473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_59 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (82053443445361 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441637103113 / 20000000000000 : ℝ))
      (E := (cell13071 ⟨59, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (82053443445361 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441637103113 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13072_40 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (82693975295651 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207996588191 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨40, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (82693975295651 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207996588191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_41 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (4133002616307 / 5000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2208000588907 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨41, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (4133002616307 / 5000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2208000588907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_42 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (16525230571517 / 20000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (441600922909 / 20000000000000 : ℝ))
      (E := (cell13072 ⟨42, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (16525230571517 / 20000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (441600922909 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_43 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (82592276860499 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (552002151261 / 25000000000000 : ℝ))
      (E := (cell13072 ⟨43, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (82592276860499 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (552002151261 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_44 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (4127921215277 / 5000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2208012617791 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨44, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (4127921215277 / 5000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2208012617791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_45 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (82524595163519 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2208016651141 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨45, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (82524595163519 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2208016651141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_46 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (82490789405389 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2208020644319 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨46, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (82490789405389 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2208020644319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_47 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (20614251750563 / 25000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (220802465413 / 10000000000000 : ℝ))
      (E := (cell13072 ⟨47, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (20614251750563 / 25000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (220802465413 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_48 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (82423247925351 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1104014339147 / 50000000000000 : ℝ))
      (E := (cell13072 ⟨48, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (82423247925351 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1104014339147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_49 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (82389512146077 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2208032714313 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨49, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (82389512146077 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2208032714313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_50 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (41177899817981 / 50000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2208036700463 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨50, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (41177899817981 / 50000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2208036700463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_51 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (2058052759167 / 2500000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2208040751837 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨51, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (2058052759167 / 2500000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2208040751837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_52 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (2571513884689 / 3125000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (138002796703 / 6250000000000 : ℝ))
      (E := (cell13072 ⟨52, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (2571513884689 / 3125000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (138002796703 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_53 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (41127400719011 / 50000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (17664389939 / 800000000000 : ℝ))
      (E := (cell13072 ⟨53, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (41127400719011 / 50000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (17664389939 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_54 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (822211817227 / 1000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (110402639639 / 5000000000000 : ℝ))
      (E := (cell13072 ⟨54, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (822211817227 / 1000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (110402639639 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_55 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (82187585136317 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (220805677651 / 10000000000000 : ℝ))
      (E := (cell13072 ⟨55, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (82187585136317 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (220805677651 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_56 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (5134625728203 / 6250000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1104030403923 / 50000000000000 : ℝ))
      (E := (cell13072 ⟨56, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (5134625728203 / 6250000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1104030403923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_57 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (20530115310001 / 25000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2208064823509 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨57, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (20530115310001 / 25000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2208064823509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_58 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (82086933875233 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2208068819123 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨58, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (82086933875233 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2208068819123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_59 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (2051335738243 / 2500000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (441614569867 / 20000000000000 : ℝ))
      (E := (cell13072 ⟨59, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (2051335738243 / 2500000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (441614569867 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13073_40 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (82693961266631 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (110394198063 / 5000000000000 : ℝ))
      (E := (cell13073 ⟨40, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (82693961266631 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (110394198063 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_41 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (20665009575811 / 25000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207887959269 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨41, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (20665009575811 / 25000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207887959269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_42 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (10328267355101 / 12500000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207891982247 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨42, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (10328267355101 / 12500000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207891982247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_43 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (16518452569967 / 20000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (1103948014493 / 50000000000000 : ℝ))
      (E := (cell13073 ⟨43, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (16518452569967 / 20000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (1103948014493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_44 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (16511682060197 / 20000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207900039187 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨44, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (16511682060197 / 20000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207900039187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_45 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (20631145291267 / 25000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207904011139 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨45, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (20631145291267 / 25000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207904011139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_46 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (82490775413037 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551977015191 / 25000000000000 : ℝ))
      (E := (cell13073 ⟨46, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (82490775413037 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551977015191 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_47 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (41228496507997 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (275989008521 / 12500000000000 : ℝ))
      (E := (cell13073 ⟨47, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (41228496507997 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (275989008521 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_48 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (41211616972591 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551979022493 / 25000000000000 : ℝ))
      (E := (cell13073 ⟨48, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (41211616972591 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551979022493 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_49 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (10298687271499 / 12500000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207920064683 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨49, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (10298687271499 / 12500000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207920064683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_50 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (20588946416989 / 25000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (1103962053779 / 50000000000000 : ℝ))
      (E := (cell13073 ⟨50, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (20588946416989 / 25000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (1103962053779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_51 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (82322096404749 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207928097669 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨51, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (82322096404749 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207928097669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_52 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (41144215177093 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (275991518743 / 12500000000000 : ℝ))
      (E := (cell13073 ⟨52, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (41144215177093 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (275991518743 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_53 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (41127393744113 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207936142939 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨53, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (41127393744113 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207936142939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_54 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (82221167778963 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207940132149 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨54, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (82221167778963 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207940132149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_55 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (20546892799659 / 25000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (44158883459 / 2000000000000 : ℝ))
      (E := (cell13073 ⟨55, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (20546892799659 / 25000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (44158883459 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_56 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (1283656214369 / 1562500000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (441589640459 / 20000000000000 : ℝ))
      (E := (cell13073 ⟨56, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (1283656214369 / 1562500000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (441589640459 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_57 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (41060223657209 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (220795221601 / 10000000000000 : ℝ))
      (E := (cell13073 ⟨57, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (41060223657209 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (220795221601 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_58 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (82086919955687 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551989052431 / 25000000000000 : ℝ))
      (E := (cell13073 ⟨58, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (82086919955687 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551989052431 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_59 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (8205341561621 / 10000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207960238081 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨59, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (8205341561621 / 10000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207960238081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13074_40 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (82693947239759 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (551942847211 / 25000000000000 : ℝ))
      (E := (cell13074 ⟨40, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (82693947239759 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (551942847211 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_41 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (16532004856499 / 20000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207775384171 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨41, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (16532004856499 / 20000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207775384171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_42 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (82626124826177 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (68993106391 / 3125000000000 : ℝ))
      (E := (cell13074 ⟨42, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (82626124826177 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (68993106391 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_43 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (82592248841317 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (137986461863 / 6250000000000 : ℝ))
      (E := (cell13074 ⟨43, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (82592248841317 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (137986461863 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_44 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (5159899768661 / 6250000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207787397441 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨44, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (5159899768661 / 6250000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207787397441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_45 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (82524567168761 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (551947856443 / 25000000000000 : ℝ))
      (E := (cell13074 ⟨45, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (82524567168761 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (551947856443 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_46 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (20622690355707 / 25000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (1103897707011 / 50000000000000 : ℝ))
      (E := (cell13074 ⟨46, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (20622690355707 / 25000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (1103897707011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_47 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (41228489515939 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (275974934743 / 12500000000000 : ℝ))
      (E := (cell13074 ⟨47, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (41228489515939 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (275974934743 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_48 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (41211609983577 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207803497387 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨48, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (41211609983577 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207803497387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_49 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (5149342762503 / 6250000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (275975933723 / 12500000000000 : ℝ))
      (E := (cell13074 ⟨49, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (5149342762503 / 6250000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (275975933723 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_50 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (8235577170209 / 10000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (275976438799 / 12500000000000 : ℝ))
      (E := (cell13074 ⟨50, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (8235577170209 / 10000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (275976438799 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_51 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (20580520611239 / 25000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207815498281 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨51, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (20580520611239 / 25000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207815498281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_52 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (41144208200231 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207819548381 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨52, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (41144208200231 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207819548381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_53 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (16450954708113 / 20000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207823539247 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨53, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (16450954708113 / 20000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207823539247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_54 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (41110576918681 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207827585483 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨54, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (41110576918681 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207827585483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_55 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (82187557263089 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (441566313027 / 20000000000000 : ℝ))
      (E := (cell13074 ⟨55, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (82187557263089 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (441566313027 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_56 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (82153983790119 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207835592487 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨56, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (82153983790119 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207835592487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_57 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (20530108347741 / 25000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (1103919802129 / 50000000000000 : ℝ))
      (E := (cell13074 ⟨57, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (20530108347741 / 25000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (1103919802129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_58 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (41043453019137 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (220784359607 / 10000000000000 : ℝ))
      (E := (cell13074 ⟨58, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (41043453019137 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (220784359607 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_59 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (641042200819 / 781250000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (551961905643 / 25000000000000 : ℝ))
      (E := (cell13074 ⟨59, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (641042200819 / 781250000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (551961905643 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

end BstLean.Part268
