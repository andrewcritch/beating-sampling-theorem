import BstLean.Part268CellShard0Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12350_0 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (16816287185573 / 20000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (45940839683 / 2000000000000 : ℝ))
      (E := (cell12350 ⟨0, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (16816287185573 / 20000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (45940839683 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_1 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (42023173231313 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (143565372139 / 6250000000000 : ℝ))
      (E := (cell12350 ⟨1, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (42023173231313 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (143565372139 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_2 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (16802256418763 / 20000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (229704996813 / 10000000000000 : ℝ))
      (E := (cell12350 ⟨2, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (16802256418763 / 20000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (229704996813 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_3 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (83976242784573 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297053977629 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨3, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (83976242784573 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297053977629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_4 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (83941228498233 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148528967067 / 50000000000000 : ℝ))
      (E := (cell12350 ⟨4, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (83941228498233 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148528967067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_5 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (41953119599161 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297061962371 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨5, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (41953119599161 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297061962371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_6 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (41935637424281 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297065955341 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨6, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (41935637424281 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297065955341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_7 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (41918167706431 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (574267480369 / 25000000000000 : ℝ))
      (E := (cell12350 ⟨7, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (41918167706431 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (574267480369 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_8 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (3352056834213 / 4000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (229707392691 / 10000000000000 : ℝ))
      (E := (cell12350 ⟨8, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (3352056834213 / 4000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (229707392691 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_9 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (1047081639253 / 1250000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297077921649 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨9, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (1047081639253 / 1250000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297077921649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_10 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (83731666232083 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297081913359 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨10, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (83731666232083 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297081913359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_11 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (83696826095517 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148542954727 / 50000000000000 : ℝ))
      (E := (cell12350 ⟨11, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (83696826095517 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148542954727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_12 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (83662010695391 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148544958547 / 50000000000000 : ℝ))
      (E := (cell12350 ⟨12, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (83662010695391 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148544958547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_13 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (16725443999347 / 20000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148546942557 / 50000000000000 : ℝ))
      (E := (cell12350 ⟨13, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (16725443999347 / 20000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148546942557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_14 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (20898113491191 / 25000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297097878207 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨14, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (20898113491191 / 25000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297097878207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_15 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (41778856282437 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148550951393 / 50000000000000 : ℝ))
      (E := (cell12350 ⟨15, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (41778856282437 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148550951393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_16 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (83522995762639 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297105848723 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨16, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (83522995762639 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297105848723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_17 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (16697660704763 / 20000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297109838141 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨17, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (16697660704763 / 20000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297109838141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_18 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (83453635814333 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297113876717 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨18, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (83453635814333 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297113876717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_19 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (5213687037519 / 6250000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148558926723 / 50000000000000 : ℝ))
      (E := (cell12350 ⟨19, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (5213687037519 / 6250000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148558926723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12351_0 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (84081419929039 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (229690239271 / 10000000000000 : ℝ))
      (E := (cell12351 ⟨0, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (84081419929039 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (229690239271 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_1 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (10505791349747 / 12500000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (229690642233 / 10000000000000 : ℝ))
      (E := (cell12351 ⟨1, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (10505791349747 / 12500000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (229690642233 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_2 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (84011266762867 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296910380983 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨2, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (84011266762867 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296910380983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_3 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (83976227786853 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296914393823 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨3, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (83976227786853 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296914393823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_4 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (83941213833269 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (287114801541 / 12500000000000 : ℝ))
      (E := (cell12351 ⟨4, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (83941213833269 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (287114801541 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_5 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (20976556216411 / 25000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296922387623 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨5, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (20976556216411 / 25000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296922387623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_6 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (83871260847699 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296926386311 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨6, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (83871260847699 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296926386311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_7 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (83836321743347 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296930358953 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨7, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (83836321743347 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296930358953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_8 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (5237587969793 / 6250000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (459386874337 / 20000000000000 : ℝ))
      (E := (cell12351 ⟨8, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (5237587969793 / 6250000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (459386874337 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_9 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (41883259066007 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (229693837451 / 10000000000000 : ℝ))
      (E := (cell12351 ⟨9, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (41883259066007 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (229693837451 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_10 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (83731653553803 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148471187547 / 50000000000000 : ℝ))
      (E := (cell12351 ⟨10, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (83731653553803 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148471187547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_11 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (83696813746719 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296946322817 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨11, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (83696813746719 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296946322817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_12 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (83661998675609 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296950340881 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨12, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (83661998675609 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296950340881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_13 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (20906802076377 / 25000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296954320107 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨13, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (20906802076377 / 25000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296954320107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_14 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (83592442601629 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (287119790649 / 12500000000000 : ℝ))
      (E := (cell12351 ⟨14, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (83592442601629 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (287119790649 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_15 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (8355770152937 / 10000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (114848115221 / 5000000000000 : ℝ))
      (E := (cell12351 ⟨15, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (8355770152937 / 10000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (114848115221 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_16 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (41761492527153 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148483161019 / 50000000000000 : ℝ))
      (E := (cell12351 ⟨16, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (41761492527153 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148483161019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_17 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (41744146571097 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296970325793 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨17, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (41744146571097 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296970325793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_18 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (41726812879483 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296974321291 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨18, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (41726812879483 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296974321291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_19 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (83418982870733 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148489156947 / 50000000000000 : ℝ))
      (E := (cell12351 ⟨19, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (83418982870733 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148489156947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12352_0 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (84081403932807 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (114838145581 / 5000000000000 : ℝ))
      (E := (cell12352 ⟨0, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (84081403932807 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (114838145581 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_1 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (42023157567939 / 50000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296766943079 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨1, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (42023157567939 / 50000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296766943079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_2 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (84011251434429 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296770904367 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨2, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (84011251434429 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296770904367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_3 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (83976212791601 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (574193730159 / 25000000000000 : ℝ))
      (E := (cell12352 ⟨3, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (83976212791601 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (574193730159 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_4 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (20985299792683 / 25000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (287097360687 / 12500000000000 : ℝ))
      (E := (cell12352 ⟨4, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (20985299792683 / 25000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (287097360687 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_5 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (83906210535351 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148391461837 / 50000000000000 : ℝ))
      (E := (cell12352 ⟨5, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (83906210535351 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148391461837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_6 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (83871246849181 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148393435127 / 50000000000000 : ℝ))
      (E := (cell12352 ⟨6, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (83871246849181 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148393435127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_7 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (83836308076133 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (143549431713 / 6250000000000 : ℝ))
      (E := (cell12352 ⟨7, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (83836308076133 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (143549431713 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_8 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (10475174272539 / 12500000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (459358973913 / 20000000000000 : ℝ))
      (E := (cell12352 ⟨8, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (10475174272539 / 12500000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (459358973913 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_9 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (83766505126009 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148399440271 / 50000000000000 : ℝ))
      (E := (cell12352 ⟨9, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (83766505126009 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148399440271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_10 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (41865820438851 / 50000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148401445033 / 50000000000000 : ℝ))
      (E := (cell12352 ⟨10, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (41865820438851 / 50000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148401445033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_11 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (83696801400057 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (574201711879 / 25000000000000 : ℝ))
      (E := (cell12352 ⟨11, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (83696801400057 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (574201711879 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_12 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (20915496664481 / 25000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (229681087609 / 10000000000000 : ℝ))
      (E := (cell12352 ⟨12, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (20915496664481 / 25000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (229681087609 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_13 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (16725439323267 / 20000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (459362973323 / 20000000000000 : ℝ))
      (E := (cell12352 ⟨13, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (16725439323267 / 20000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (459362973323 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_14 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (20898107810127 / 25000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296818825677 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨14, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (20898107810127 / 25000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296818825677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_15 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (83557690495839 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (459364563549 / 20000000000000 : ℝ))
      (E := (cell12352 ⟨15, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (83557690495839 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (459364563549 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_16 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (16704594869581 / 20000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (459365369797 / 20000000000000 : ℝ))
      (E := (cell12352 ⟨16, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (16704594869581 / 20000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (459365369797 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_17 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (2609008836327 / 3125000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296830808971 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨17, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (2609008836327 / 3125000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296830808971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_18 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (83453615705449 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (574208704907 / 25000000000000 : ℝ))
      (E := (cell12352 ⟨18, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (83453615705449 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (574208704907 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_19 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (20854743285743 / 25000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296838828169 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨19, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (20854743285743 / 25000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296838828169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12353_0 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (84081387939169 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296623540881 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨0, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (84081387939169 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296623540881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_1 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (84046299476331 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296627516473 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨1, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (84046299476331 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296627516473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_2 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (168022472217 / 200000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148315740231 / 50000000000000 : ℝ))
      (E := (cell12353 ⟨2, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (168022472217 / 200000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148315740231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_3 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (41988098899409 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148317750113 / 50000000000000 : ℝ))
      (E := (cell12353 ⟨3, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (41988098899409 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148317750113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_4 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (41970592255311 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (35884991709 / 1562500000000 : ℝ))
      (E := (cell12353 ⟨4, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (41970592255311 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (35884991709 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_5 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (20976549051861 / 25000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (287080431843 / 12500000000000 : ℝ))
      (E := (cell12353 ⟨5, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (20976549051861 / 25000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (287080431843 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_6 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (16774246570601 / 20000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (17942558321 / 781250000000 : ℝ))
      (E := (cell12353 ⟨6, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (16774246570601 / 20000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (17942558321 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_7 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (41918147205611 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296651450967 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨7, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (41918147205611 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296651450967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_8 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (83801380846197 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148327739257 / 50000000000000 : ℝ))
      (E := (cell12353 ⟨8, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (83801380846197 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148327739257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_9 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (41883246061111 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296659439749 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨9, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (41883246061111 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296659439749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_10 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (83731628203779 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148331729139 / 50000000000000 : ℝ))
      (E := (cell12353 ⟨10, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (83731628203779 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148331729139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_11 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (83696789055533 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296667425519 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨11, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (83696789055533 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296667425519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_12 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (41830987321167 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (71770983271 / 3125000000000 : ℝ))
      (E := (cell12353 ⟨12, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (41830987321167 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (71770983271 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_13 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (41813592464609 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (14354221303 / 625000000000 : ℝ))
      (E := (cell12353 ⟨13, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (41813592464609 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (14354221303 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_14 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (417962099407 / 500000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296679437767 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨14, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (417962099407 / 500000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296679437767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_15 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (2088941986607 / 2500000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (574170860691 / 25000000000000 : ℝ))
      (E := (cell12353 ⟨15, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (2088941986607 / 2500000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (574170860691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_16 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (20880740910859 / 25000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (459337485913 / 20000000000000 : ℝ))
      (E := (cell12353 ⟨16, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (20880740910859 / 25000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (459337485913 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_17 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (667906179077 / 800000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296691404019 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨17, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (667906179077 / 800000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296691404019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_18 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (41726802826891 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (91867817197 / 4000000000000 : ℝ))
      (E := (cell12353 ⟨18, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (41726802826891 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (91867817197 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_19 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (4170948170851 / 5000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148349698137 / 50000000000000 : ℝ))
      (E := (cell12353 ⟨19, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (4170948170851 / 5000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148349698137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12354_0 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (42040685974061 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (287060520619 / 12500000000000 : ℝ))
      (E := (cell12354 ⟨0, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (42040685974061 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (287060520619 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_1 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (16809256763867 / 20000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (574122035629 / 25000000000000 : ℝ))
      (E := (cell12354 ⟨1, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (16809256763867 / 20000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (574122035629 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_2 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (84011220785081 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296492167091 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨2, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (84011220785081 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296492167091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_3 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (41988091404251 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296496132597 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨3, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (41988091404251 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296496132597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_4 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (41970584926469 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296500163969 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨4, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (41970584926469 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296500163969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_5 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (262206818381 / 312500000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296504154509 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨5, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (262206818381 / 312500000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296504154509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_6 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (83871218859173 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296508112901 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨6, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (83871218859173 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296508112901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_7 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (20959070187153 / 25000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296512105509 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨7, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (20959070187153 / 25000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296512105509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_8 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (83801367514341 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (71766129393 / 3125000000000 : ℝ))
      (E := (cell12354 ⟨8, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (83801367514341 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (71766129393 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_9 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (16753295824131 / 20000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296520110117 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨9, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (16753295824131 / 20000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296520110117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_10 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (41865807766017 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (574131019933 / 25000000000000 : ℝ))
      (E := (cell12354 ⟨10, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (41865807766017 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (574131019933 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_11 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (16739355342629 / 20000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296528114863 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨11, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (16739355342629 / 20000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296528114863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_12 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (2091549065721 / 2500000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (574133026657 / 25000000000000 : ℝ))
      (E := (cell12354 ⟨12, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (2091549065721 / 2500000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (574133026657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_13 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (41813586622077 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (287067007733 / 12500000000000 : ℝ))
      (E := (cell12354 ⟨13, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (41813586622077 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (287067007733 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_14 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (41796204262153 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148270051681 / 50000000000000 : ℝ))
      (E := (cell12354 ⟨14, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (41796204262153 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148270051681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_15 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (41778834217347 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (574136015807 / 25000000000000 : ℝ))
      (E := (cell12354 ⟨15, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (41778834217347 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (574136015807 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_16 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (41761476470449 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148274031891 / 50000000000000 : ℝ))
      (E := (cell12354 ⟨16, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (41761476470449 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148274031891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_17 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (20872065502169 / 25000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (229655205277 / 10000000000000 : ℝ))
      (E := (cell12354 ⟨17, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (20872065502169 / 25000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (229655205277 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_18 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (16690719120793 / 20000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148278017897 / 50000000000000 : ℝ))
      (E := (cell12354 ⟨18, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (16690719120793 / 20000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148278017897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_19 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (41709476846439 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (229656007643 / 10000000000000 : ℝ))
      (E := (cell12354 ⟨19, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (41709476846439 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (229656007643 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12355_0 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (21020338989917 / 25000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296344899379 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨0, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (21020338989917 / 25000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296344899379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_1 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (8404626816489 / 10000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296348879003 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨1, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (8404626816489 / 10000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296348879003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_2 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (8401120546417 / 10000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (287044106077 / 12500000000000 : ℝ))
      (E := (cell12355 ⟨2, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (8401120546417 / 10000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (287044106077 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_3 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (83976167820653 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148178437797 / 50000000000000 : ℝ))
      (E := (cell12355 ⟨3, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (83976167820653 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148178437797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_4 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (83941155197679 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296360853543 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨4, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (83941155197679 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296360853543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_5 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (4195308377939 / 5000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296364849297 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨5, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (4195308377939 / 5000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296364849297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_6 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (83871204867683 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296368813693 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨6, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (83871204867683 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296368813693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_7 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (41918133544151 / 50000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148186406549 / 50000000000000 : ℝ))
      (E := (cell12355 ⟨7, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (41918133544151 / 50000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148186406549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_8 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (16760270836949 / 20000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296376855749 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨8, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (16760270836949 / 20000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296376855749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_9 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (16753293224261 / 20000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296380833663 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨9, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (16753293224261 / 20000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296380833663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_10 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (16746320572493 / 20000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296384812439 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨10, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (16746320572493 / 20000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296384812439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_11 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (20924191093223 / 25000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148194399743 / 50000000000000 : ℝ))
      (E := (cell12355 ⟨11, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (20924191093223 / 25000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148194399743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_12 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (522887191359 / 625000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296392801959 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨12, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (522887191359 / 625000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296392801959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_13 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (10453395195143 / 12500000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296396826767 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨13, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (10453395195143 / 12500000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296396826767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_14 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (10449049646153 / 12500000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (35881262851 / 1562500000000 : ℝ))
      (E := (cell12355 ⟨14, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (10449049646153 / 12500000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (35881262851 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_15 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (83557657407079 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (229640479539 / 10000000000000 : ℝ))
      (E := (cell12355 ⟨15, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (83557657407079 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (229640479539 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_16 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (83522942240291 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (459281761957 / 20000000000000 : ℝ))
      (E := (cell12355 ⟨16, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (83522942240291 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (459281761957 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_17 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (41744125817309 / 50000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296412755223 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨17, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (41744125817309 / 50000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296412755223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_18 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (41726792777999 / 50000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (18371334029 / 800000000000 : ℝ))
      (E := (cell12355 ⟨18, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (41726792777999 / 50000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (18371334029 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_19 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (5213683998159 / 6250000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296420752201 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨19, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (5213683998159 / 6250000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296420752201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12356_0 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (42040669986903 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296205686389 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨0, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (42040669986903 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296205686389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_1 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (42023126256497 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148104834071 / 50000000000000 : ℝ))
      (E := (cell12356 ⟨1, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (42023126256497 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148104834071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_2 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (42005595072883 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296213640679 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨2, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (42005595072883 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296213640679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_3 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (8397615283527 / 10000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296217671373 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨3, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (8397615283527 / 10000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296217671373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_4 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (20985285136211 / 25000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148110826917 / 50000000000000 : ℝ))
      (E := (cell12356 ⟨4, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (20985285136211 / 25000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148110826917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_5 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (83906153238023 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296225654891 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨5, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (83906153238023 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296225654891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_6 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (41935595439267 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148114812691 / 50000000000000 : ℝ))
      (E := (cell12356 ⟨6, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (41935595439267 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148114812691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_7 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (83836253430293 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296233631671 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨7, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (83836253430293 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296233631671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_8 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (83801340857407 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (459247524807 / 20000000000000 : ℝ))
      (E := (cell12356 ⟨8, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (83801340857407 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (459247524807 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_9 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (83766453124173 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (574060402597 / 25000000000000 : ℝ))
      (E := (cell12356 ⟨9, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (83766453124173 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (574060402597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_10 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (83731590195073 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (229624559839 / 10000000000000 : ℝ))
      (E := (cell12356 ⟨10, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (83731590195073 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (229624559839 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_11 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (3347870081391 / 4000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (45924991909 / 2000000000000 : ℝ))
      (E := (cell12356 ⟨11, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (3347870081391 / 4000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (45924991909 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_12 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (41830969304067 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296253608721 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨12, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (41830969304067 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296253608721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_13 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (83627149880187 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296257587033 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨13, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (83627149880187 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296257587033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_14 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (41796192908077 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296261595073 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨14, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (41796192908077 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296261595073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_15 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (16711529276287 / 20000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (18370124649 / 800000000000 : ℝ))
      (E := (cell12356 ⟨15, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (16711529276287 / 20000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (18370124649 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_16 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (41761465770807 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148134775639 / 50000000000000 : ℝ))
      (E := (cell12356 ⟨16, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (41761465770807 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148134775639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_17 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (83488241262449 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (143517098097 / 6250000000000 : ℝ))
      (E := (cell12356 ⟨17, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (83488241262449 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (143517098097 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_18 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (83453575509879 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148138791711 / 50000000000000 : ℝ))
      (E := (cell12356 ⟨18, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (83453575509879 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148138791711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_19 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (41709467125009 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (91851261601 / 4000000000000 : ℝ))
      (E := (cell12356 ⟨19, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (41709467125009 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (91851261601 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12357_0 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (42040661995267 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (459213305197 / 20000000000000 : ℝ))
      (E := (cell12357 ⟨0, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (42040661995267 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (459213305197 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_1 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (84046236863647 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (574017627483 / 25000000000000 : ℝ))
      (E := (cell12357 ⟨1, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (84046236863647 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (574017627483 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_2 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (84011174829871 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148037242729 / 50000000000000 : ℝ))
      (E := (cell12357 ⟨2, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (84011174829871 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148037242729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_3 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (83976137852353 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296078519937 / 100000000000000 : ℝ))
      (E := (cell12357 ⟨3, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (83976137852353 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296078519937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_4 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (41970562947217 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (91843300279 / 4000000000000 : ℝ))
      (E := (cell12357 ⟨4, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (41970562947217 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (91843300279 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_5 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (83906138919649 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (229608645551 / 10000000000000 : ℝ))
      (E := (cell12357 ⟨5, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (83906138919649 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (229608645551 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_6 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (41935588445863 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148045245027 / 50000000000000 : ℝ))
      (E := (cell12357 ⟨6, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (41935588445863 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148045245027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_7 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (83836239774583 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (459218889071 / 20000000000000 : ℝ))
      (E := (cell12357 ⟨7, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (83836239774583 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (459218889071 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_8 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (10475165941541 / 12500000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (574024611359 / 25000000000000 : ℝ))
      (E := (cell12357 ⟨8, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (10475165941541 / 12500000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (574024611359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_9 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (41883220064629 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148051220147 / 50000000000000 : ℝ))
      (E := (cell12357 ⟨9, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (41883220064629 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148051220147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_10 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (163538237363 / 195312500000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296106437589 / 100000000000000 : ℝ))
      (E := (cell12357 ⟨10, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (163538237363 / 195312500000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296106437589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_11 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (10462092462349 / 12500000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148055222363 / 50000000000000 : ℝ))
      (E := (cell12357 ⟨11, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (10462092462349 / 12500000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148055222363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_12 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (83661926600921 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296114468863 / 100000000000000 : ℝ))
      (E := (cell12357 ⟨12, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (83661926600921 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296114468863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_13 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (41813569100641 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148059229411 / 50000000000000 : ℝ))
      (E := (cell12357 ⟨13, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (41813569100641 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148059229411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_14 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (16718474893019 / 20000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (287015302649 / 12500000000000 : ℝ))
      (E := (cell12357 ⟨14, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (16718474893019 / 20000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (287015302649 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_15 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (41778817678881 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148063210217 / 50000000000000 : ℝ))
      (E := (cell12357 ⟨15, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (41778817678881 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148063210217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_16 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (83522920844867 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (28701630057 / 1250000000000 : ℝ))
      (E := (cell12357 ⟨16, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (83522920844867 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (28701630057 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_17 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (83488230892169 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296134437587 / 100000000000000 : ℝ))
      (E := (cell12357 ⟨17, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (83488230892169 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296134437587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_18 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (10431695683201 / 12500000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148069204397 / 50000000000000 : ℝ))
      (E := (cell12357 ⟨18, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (10431695683201 / 12500000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148069204397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_19 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (834189245313 / 1000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (459228476337 / 20000000000000 : ℝ))
      (E := (cell12357 ⟨19, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (834189245313 / 1000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (459228476337 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12358_0 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (21020327002463 / 25000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (286990927271 / 12500000000000 : ℝ))
      (E := (cell12358 ⟨0, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (21020327002463 / 25000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (286990927271 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_1 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (5252888826053 / 6250000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (286991425547 / 12500000000000 : ℝ))
      (E := (cell12358 ⟨1, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (5252888826053 / 6250000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (286991425547 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_2 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (84011159516481 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (114796772039 / 5000000000000 : ℝ))
      (E := (cell12358 ⟨2, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (84011159516481 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (114796772039 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_3 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (839761228719 / 1000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (286992427661 / 12500000000000 : ℝ))
      (E := (cell12358 ⟨3, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (839761228719 / 1000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (286992427661 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_4 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (83941111246447 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (286992926621 / 12500000000000 : ℝ))
      (E := (cell12358 ⟨4, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (83941111246447 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (286992926621 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_5 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (83906124603657 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (229594742483 / 10000000000000 : ℝ))
      (E := (cell12358 ⟨5, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (83906124603657 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (229594742483 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_6 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (83871162907259 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2295951407709 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨6, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (83871162907259 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2295951407709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_7 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (83836226121173 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2295955370027 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨7, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (83836226121173 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2295955370027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_8 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (83801314209507 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1147979688957 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨8, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (83801314209507 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1147979688957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_9 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (83766427136559 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2295963381367 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨9, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (83766427136559 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2295963381367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_10 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (41865782433407 / 50000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2295967388043 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨10, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (41865782433407 / 50000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2295967388043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_11 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (83696727364943 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2295971347317 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨11, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (83696727364943 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2295971347317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_12 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (41830957297901 / 50000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1147987691191 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨12, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (41830957297901 / 50000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1147987691191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_13 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (83627126524429 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2295979325977 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨13, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (83627126524429 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2295979325977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_14 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (5224522694753 / 6250000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1147991679461 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨14, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (5224522694753 / 6250000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1147991679461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_15 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (4177881216803 / 5000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1147993656659 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨15, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (4177881216803 / 5000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1147993656659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_16 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (83522910150049 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2295991311483 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨16, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (83522910150049 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2295991311483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_17 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (83488220523777 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2295995359329 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨17, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (83488220523777 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2295995359329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_18 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (16690711084637 / 20000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1147999673067 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨18, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (16690711084637 / 20000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1147999673067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_19 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (83418914814389 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148001667701 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨19, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (83418914814389 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148001667701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12359_0 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (1051016150397 / 1250000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147894210357 / 50000000000000 : ℝ))
      (E := (cell12359 ⟨0, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (1051016150397 / 1250000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147894210357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_1 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (84046205572597 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295792409273 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨1, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (84046205572597 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295792409273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_2 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (42005572102799 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295796391001 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨2, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (42005572102799 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295796391001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_3 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (10497013486739 / 12500000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147900187713 / 50000000000000 : ℝ))
      (E := (cell12359 ⟨3, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (10497013486739 / 12500000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147900187713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_4 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (41970548300441 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295804371817 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨4, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (41970548300441 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295804371817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_5 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (41953055145023 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295808389179 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨5, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (41953055145023 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295808389179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_6 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (20967787231283 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295812378351 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨6, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (20967787231283 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295812378351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_7 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (83836212470061 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (286977043469 / 12500000000000 : ℝ))
      (E := (cell12359 ⟨7, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (83836212470061 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (286977043469 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_8 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (83801300888943 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295820363511 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨8, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (83801300888943 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295820363511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_9 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (20941603536519 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (286978046953 / 12500000000000 : ℝ))
      (E := (cell12359 ⟨9, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (20941603536519 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (286978046953 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_10 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (20932888051487 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147914166869 / 50000000000000 : ℝ))
      (E := (cell12359 ⟨10, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (20932888051487 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147914166869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_11 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (20924178758307 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (459166472251 / 20000000000000 : ℝ))
      (E := (cell12359 ⟨11, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (20924178758307 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (459166472251 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_12 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (3346476103711 / 4000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295836349283 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨12, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (3346476103711 / 4000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295836349283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_13 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (20906778712407 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295840362737 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨13, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (20906778712407 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295840362737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_14 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (8359235176901 / 10000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295844350167 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨14, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (8359235176901 / 10000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295844350167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_15 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (41778806658163 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (573962079477 / 25000000000000 : ℝ))
      (E := (cell12359 ⟨15, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (41778806658163 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (573962079477 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_16 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (2088072486429 / 2500000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295852330199 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨16, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (2088072486429 / 2500000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295852330199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_17 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (41744105078637 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295856334779 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨17, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (41744105078637 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295856334779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_18 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (83453545382609 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295860337249 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨18, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (83453545382609 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295860337249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_19 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (20854726274821 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295864284739 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨19, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (20854726274821 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295864284739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12360_0 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (1313769938379 / 1562500000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295649475851 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨0, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (1313769938379 / 1562500000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295649475851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_1 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (84046189930893 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295653466827 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨1, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (84046189930893 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295653466827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_2 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (84011128897221 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147828725883 / 50000000000000 : ℝ))
      (E := (cell12360 ⟨2, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (84011128897221 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147828725883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_3 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (20994023229597 / 25000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147830720099 / 50000000000000 : ℝ))
      (E := (cell12360 ⟨3, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (20994023229597 / 25000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147830720099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_4 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (4197054097887 / 5000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295665441387 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨4, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (4197054097887 / 5000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295665441387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_5 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (16781219195763 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (45913388129 / 2000000000000 : ℝ))
      (E := (cell12360 ⟨5, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (16781219195763 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (45913388129 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_6 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (83871134945343 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295673401981 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨6, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (83871134945343 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295673401981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_7 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (41918099410623 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295677436469 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨7, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (41918099410623 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295677436469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_8 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (16760257514127 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (573920350557 / 25000000000000 : ℝ))
      (E := (cell12360 ⟨8, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (16760257514127 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (573920350557 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_9 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (83766401157809 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147842711533 / 50000000000000 : ℝ))
      (E := (cell12360 ⟨9, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (83766401157809 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147842711533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_10 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (16746307909451 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147844695347 / 50000000000000 : ℝ))
      (E := (cell12360 ⟨10, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (16746307909451 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147844695347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_11 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (41848351351823 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295693370477 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨11, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (41848351351823 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295693370477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_12 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (522886816199 / 625000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147848684783 / 50000000000000 : ℝ))
      (E := (cell12360 ⟨12, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (522886816199 / 625000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147848684783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_13 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (41813551588439 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (459140278973 / 20000000000000 : ℝ))
      (E := (cell12360 ⟨13, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (41813551588439 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (459140278973 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_14 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (83592340423983 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (573926348731 / 25000000000000 : ℝ))
      (E := (cell12360 ⟨14, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (83592340423983 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (573926348731 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_15 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (41778801149281 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (573927344019 / 25000000000000 : ℝ))
      (E := (cell12360 ⟨15, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (41778801149281 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (573927344019 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_16 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (83522888766199 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295713344409 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨16, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (83522888766199 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295713344409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_17 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (83488199792657 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (114785868197 / 5000000000000 : ℝ))
      (E := (cell12360 ⟨17, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (83488199792657 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (114785868197 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_18 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (2086338383597 / 2500000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295721382137 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨18, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (2086338383597 / 2500000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295721382137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_19 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (41709447692993 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (459145069227 / 20000000000000 : ℝ))
      (E := (cell12360 ⟨19, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (41709447692993 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (459145069227 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12361_0 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (84081260083341 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (114775529179 / 5000000000000 : ℝ))
      (E := (cell12361 ⟨0, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (84081260083341 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (114775529179 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_1 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (10505771786467 / 12500000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295514577039 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨1, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (10505771786467 / 12500000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295514577039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_2 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (21002778397837 / 25000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295518565257 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨2, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (21002778397837 / 25000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295518565257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_3 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (83976077945327 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295522557761 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨3, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (83976077945327 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295522557761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_4 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (4197053365851 / 5000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (459105312763 / 20000000000000 : ℝ))
      (E := (cell12361 ⟨4, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (4197053365851 / 5000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (459105312763 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_5 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (16781216333993 / 20000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (286941316817 / 12500000000000 : ℝ))
      (E := (cell12361 ⟨5, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (16781216333993 / 20000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (286941316817 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_6 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (41935560483947 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (459106907303 / 20000000000000 : ℝ))
      (E := (cell12361 ⟨6, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (41935560483947 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (459106907303 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_7 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (83836185174729 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (143471157519 / 6250000000000 : ℝ))
      (E := (cell12361 ⟨7, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (83836185174729 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (143471157519 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_8 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (83801274254583 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (573885638007 / 25000000000000 : ℝ))
      (E := (cell12361 ⟨8, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (83801274254583 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (573885638007 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_9 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (20941597042939 / 25000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (143471657731 / 6250000000000 : ℝ))
      (E := (cell12361 ⟨9, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (20941597042939 / 25000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (143471657731 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_10 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (5233220430671 / 6250000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (1147775250451 / 50000000000000 : ℝ))
      (E := (cell12361 ⟨10, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (5233220430671 / 6250000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (1147775250451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_11 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (20924172594049 / 25000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (45911089821 / 2000000000000 : ℝ))
      (E := (cell12361 ⟨11, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (20924172594049 / 25000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (45911089821 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_12 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (20915469648249 / 25000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (229555850129 / 10000000000000 : ℝ))
      (E := (cell12361 ⟨12, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (20915469648249 / 25000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (229555850129 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_13 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (41813545753089 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295562480443 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨13, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (41813545753089 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295562480443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_14 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (41796164540483 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (573891623299 / 25000000000000 : ℝ))
      (E := (cell12361 ⟨14, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (41796164540483 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (573891623299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_15 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (41778795641383 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (91822819513 / 4000000000000 : ℝ))
      (E := (cell12361 ⟨15, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (41778795641383 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (91822819513 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_16 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (41761439038583 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (143473404401 / 6250000000000 : ℝ))
      (E := (cell12361 ⟨16, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (41761439038583 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (143473404401 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_17 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (10436023678741 / 12500000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (459115700997 / 20000000000000 : ℝ))
      (E := (cell12361 ⟨17, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (10436023678741 / 12500000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (459115700997 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_18 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (41726762653499 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295582480803 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨18, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (41726762653499 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295582480803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_19 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (83418885674493 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (18364691691 / 800000000000 : ℝ))
      (E := (cell12361 ⟨19, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (83418885674493 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (18364691691 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12362_0 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (42040622056507 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295371743901 / 100000000000000 : ℝ))
      (E := (cell12362 ⟨0, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (42040622056507 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295371743901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_1 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (672369269241 / 800000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (229537573991 / 10000000000000 : ℝ))
      (E := (cell12362 ⟨1, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (672369269241 / 800000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (229537573991 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_2 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (84011098287979 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147689865737 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨2, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (84011098287979 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147689865737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_3 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (83976062974729 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (459076745623 / 20000000000000 : ℝ))
      (E := (cell12362 ⟨3, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (83976062974729 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (459076745623 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_4 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (262315789621 / 312500000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147693869551 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨4, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (262315789621 / 312500000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147693869551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_5 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (41953033681747 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147695857773 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨5, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (41953033681747 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147695857773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_6 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (83871106992783 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147697862019 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨6, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (83871106992783 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147697862019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_7 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (83836171530509 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (573849928783 / 25000000000000 : ℝ))
      (E := (cell12362 ⟨7, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (83836171530509 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (573849928783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_8 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (83801260940787 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295403696987 / 100000000000000 : ℝ))
      (E := (cell12362 ⟨8, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (83801260940787 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295403696987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_9 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (41883187593959 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147703867749 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨9, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (41883187593959 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147703867749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_10 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (8373151423639 / 10000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295411722373 / 100000000000000 : ℝ))
      (E := (cell12362 ⟨10, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (8373151423639 / 10000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295411722373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_11 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (83696678050879 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147707861487 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨11, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (83696678050879 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147707861487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_12 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (83661866596243 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147709843199 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨12, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (83661866596243 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147709843199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_13 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (10453384979691 / 12500000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295423677551 / 100000000000000 : ℝ))
      (E := (cell12362 ⟨13, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (10453384979691 / 12500000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295423677551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_14 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (83592317739957 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295427703087 / 100000000000000 : ℝ))
      (E := (cell12362 ⟨14, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (83592317739957 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295427703087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_15 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (83557580268939 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147715826577 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨15, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (83557580268939 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147715826577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_16 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (4176143369503 / 5000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295435650069 / 100000000000000 : ℝ))
      (E := (cell12362 ⟨16, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (4176143369503 / 5000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295435650069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_17 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (41744089534543 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (71732488799 / 3125000000000 : ℝ))
      (E := (cell12362 ⟨17, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (41744089534543 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (71732488799 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_18 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (83453515271961 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147721816623 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨18, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (83453515271961 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147721816623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_19 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (41709437982403 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (459089526091 / 20000000000000 : ℝ))
      (E := (cell12362 ⟨19, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (41709437982403 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (459089526091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12363_0 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (84081228145273 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147616507297 / 50000000000000 : ℝ))
      (E := (cell12363 ⟨0, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (84081228145273 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147616507297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_1 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (84046143021059 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147618506621 / 50000000000000 : ℝ))
      (E := (cell12363 ⟨1, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (84046143021059 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147618506621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_2 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (42005541493557 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295241008239 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨2, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (42005541493557 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295241008239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_3 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (1312125750103 / 1562500000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (229524500911 / 10000000000000 : ℝ))
      (E := (cell12363 ⟨3, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (1312125750103 / 1562500000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (229524500911 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_4 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (83941038042841 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295248967249 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨4, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (83941038042841 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295248967249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_5 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (41953026529701 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (18362024059 / 800000000000 : ℝ))
      (E := (cell12363 ⟨5, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (41953026529701 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (18362024059 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_6 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (83871093020009 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (459051392911 / 20000000000000 : ℝ))
      (E := (cell12363 ⟨6, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (83871093020009 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (459051392911 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_7 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (16767231577717 / 20000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295260963019 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨7, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (16767231577717 / 20000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295260963019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_8 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (41900623814623 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295264953033 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨8, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (41900623814623 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295264953033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_9 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (83766362206293 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147634471253 / 50000000000000 : ℝ))
      (E := (cell12363 ⟨9, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (83766362206293 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147634471253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_10 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (10466437698027 / 12500000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295272939091 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨10, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (10466437698027 / 12500000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295272939091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_11 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (20924166431923 / 25000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295276950189 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨11, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (20924166431923 / 25000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295276950189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_12 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (83661854601581 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295280924893 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨12, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (83661854601581 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295280924893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_13 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (83627068170927 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295284928113 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨13, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (83627068170927 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295284928113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_14 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (83592306400957 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147644454197 / 50000000000000 : ℝ))
      (E := (cell12363 ⟨14, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (83592306400957 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147644454197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_15 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (83557569257079 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (459058586039 / 20000000000000 : ℝ))
      (E := (cell12363 ⟨15, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (83557569257079 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (459058586039 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_16 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (83522856704881 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295296941521 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨16, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (83522856704881 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295296941521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_17 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (83488168710129 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (57382522251 / 2500000000000 : ℝ))
      (E := (cell12363 ⟨17, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (83488168710129 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (57382522251 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_18 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (8345350523877 / 10000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147652448833 / 50000000000000 : ℝ))
      (E := (cell12363 ⟨18, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (8345350523877 / 10000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147652448833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_19 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (83418866256923 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147654455801 / 50000000000000 : ℝ))
      (E := (cell12363 ⟨19, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (83418866256923 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147654455801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12364_0 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (84081212180119 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573773584471 / 25000000000000 : ℝ))
      (E := (cell12364 ⟨0, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (84081212180119 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573773584471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_1 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (84046127389537 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295098339239 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨1, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (84046127389537 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295098339239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_2 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (5250691730547 / 6250000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (286887792217 / 12500000000000 : ℝ))
      (E := (cell12364 ⟨2, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (5250691730547 / 6250000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (286887792217 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_3 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (83976033040917 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (4482629463 / 195312500000 : ℝ))
      (E := (cell12364 ⟨3, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (83976033040917 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (4482629463 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_4 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (41970511704691 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295110306127 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨4, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (41970511704691 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295110306127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_5 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (83906038757689 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295114294239 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨5, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (83906038757689 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295114294239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_6 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (20967769762393 / 25000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295118315983 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨6, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (20967769762393 / 25000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295118315983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_7 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (83836144248957 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (1147561131983 / 50000000000000 : ℝ))
      (E := (cell12364 ⟨7, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (83836144248957 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (1147561131983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_8 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (83801234319959 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (459025252441 / 20000000000000 : ℝ))
      (E := (cell12364 ⟨8, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (83801234319959 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (459025252441 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_9 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (83766349226881 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295130260691 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨9, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (83766349226881 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295130260691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_10 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (16746297786843 / 20000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573783566769 / 25000000000000 : ℝ))
      (E := (cell12364 ⟨10, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (16746297786843 / 20000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573783566769 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_11 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (83696653406637 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295138288759 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨11, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (83696653406637 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295138288759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_12 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (5228865163063 / 6250000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (459028454967 / 20000000000000 : ℝ))
      (E := (cell12364 ⟨12, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (5228865163063 / 6250000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (459028454967 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_13 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (669016452051 / 800000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295146232129 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨13, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (669016452051 / 800000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295146232129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_14 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (16718459012793 / 20000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573787556331 / 25000000000000 : ℝ))
      (E := (cell12364 ⟨14, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (16718459012793 / 20000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573787556331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_15 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (41778779123593 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295154260821 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨15, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (41778779123593 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295154260821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_16 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (20880711505407 / 25000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (91806329139 / 4000000000000 : ℝ))
      (E := (cell12364 ⟨16, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (20880711505407 / 25000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (91806329139 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_17 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (83488158353059 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2868952813 / 125000000000 : ℝ))
      (E := (cell12364 ⟨17, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (83488158353059 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2868952813 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_18 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (83453495207423 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573791553967 / 25000000000000 : ℝ))
      (E := (cell12364 ⟨18, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (83453495207423 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573791553967 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_19 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (16683771310169 / 20000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (459034049319 / 20000000000000 : ℝ))
      (E := (cell12364 ⟨19, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (16683771310169 / 20000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (459034049319 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12365_0 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (84081196217551 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (573738928443 / 25000000000000 : ℝ))
      (E := (cell12365 ⟨0, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (84081196217551 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (573738928443 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_1 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (1050576397007 / 1250000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147479858949 / 50000000000000 : ℝ))
      (E := (cell12365 ⟨1, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (1050576397007 / 1250000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147479858949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_2 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (21002763098223 / 25000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2294963719963 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨2, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (21002763098223 / 25000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2294963719963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_3 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (83976018077703 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2294967671643 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨3, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (83976018077703 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2294967671643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_4 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (41970504389171 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (573742924467 / 25000000000000 : ℝ))
      (E := (cell12365 ⟨4, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (41970504389171 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (573742924467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_5 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (41953012229177 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (91799027677 / 4000000000000 : ℝ))
      (E := (cell12365 ⟨5, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (41953012229177 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (91799027677 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_6 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (655242695949 / 781250000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2294979662489 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨6, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (655242695949 / 781250000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2294979662489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_7 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (10479516326453 / 12500000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2294983675913 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨7, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (10479516326453 / 12500000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2294983675913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_8 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (41900610506463 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2294987682467 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨8, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (41900610506463 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2294987682467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_9 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (41883168124841 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2294991632069 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨9, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (41883168124841 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2294991632069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_10 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (16746295257277 / 20000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2294995648319 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨10, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (16746295257277 / 20000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2294995648319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_11 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (2615520033991 / 3125000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2294999622621 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨11, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (2615520033991 / 3125000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2294999622621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_12 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (3346473224741 / 4000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295003620109 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨12, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (3346473224741 / 4000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295003620109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_13 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (2613345151371 / 3125000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295007647679 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨13, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (2613345151371 / 3125000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295007647679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_14 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (4179614186449 / 5000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147505797887 / 50000000000000 : ℝ))
      (E := (cell12365 ⟨14, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (4179614186449 / 5000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147505797887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_15 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (4177877361963 / 5000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295015645033 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨15, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (4177877361963 / 5000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295015645033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_16 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (83522835340301 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (229501962723 / 10000000000000 : ℝ))
      (E := (cell12365 ⟨16, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (83522835340301 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (229501962723 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_17 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (83488147997873 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (459004721261 / 20000000000000 : ℝ))
      (E := (cell12365 ⟨17, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (83488147997873 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (459004721261 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_18 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (83453485177921 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295027587851 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨18, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (83453485177921 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295027587851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_19 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (8341884684657 / 10000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (17929934197 / 781250000000 : ℝ))
      (E := (cell12365 ⟨19, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (8341884684657 / 10000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (17929934197 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12366_0 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (2627536883049 / 3125000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294817142259 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨0, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (2627536883049 / 3125000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294817142259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_1 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (42023048067063 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (286852643653 / 12500000000000 : ℝ))
      (E := (cell12366 ⟨1, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (42023048067063 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (286852643653 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_2 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (42005518549767 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294825154923 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨2, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (42005518549767 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294825154923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_3 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (83976003116949 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294829111029 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨3, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (83976003116949 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294829111029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_4 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (83940994149721 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147416571237 / 50000000000000 : ℝ))
      (E := (cell12366 ⟨4, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (83940994149721 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147416571237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_5 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (16781202032279 / 20000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147418571271 / 50000000000000 : ℝ))
      (E := (cell12366 ⟨5, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (16781202032279 / 20000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147418571271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_6 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (83871051115707 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294841119907 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨6, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (83871051115707 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294841119907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_7 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (16767223395317 / 20000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (286855635373 / 12500000000000 : ℝ))
      (E := (cell12366 ⟨7, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (16767223395317 / 20000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (286855635373 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_8 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (41900603854073 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147424548947 / 50000000000000 : ℝ))
      (E := (cell12366 ⟨8, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (41900603854073 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147424548947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_9 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (16753264654939 / 20000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294853114627 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨9, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (16753264654939 / 20000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294853114627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_10 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (41865731820363 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147428541411 / 50000000000000 : ℝ))
      (E := (cell12366 ⟨10, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (41865731820363 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147428541411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_11 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (20924157192729 / 25000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294861067841 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨11, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (20924157192729 / 25000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294861067841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_12 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (83661818630131 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (229486507683 / 10000000000000 : ℝ))
      (E := (cell12366 ⟨12, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (83661818630131 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (229486507683 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_13 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (10453379147927 / 12500000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294869058607 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨13, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (10453379147927 / 12500000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294869058607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_14 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (41796136198001 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (45897461557 / 2000000000000 : ℝ))
      (E := (cell12366 ⟨14, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (41796136198001 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (45897461557 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_15 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (835575362333 / 1000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294877082833 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨15, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (835575362333 / 1000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294877082833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_16 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (835228246609 / 1000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294881079637 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨16, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (835228246609 / 1000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294881079637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_17 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (20872034411143 / 25000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294885074101 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨17, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (20872034411143 / 25000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294885074101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_18 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (83453475150263 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147444535907 / 50000000000000 : ℝ))
      (E := (cell12366 ⟨18, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (83453475150263 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147444535907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_19 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (83418837144099 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (8964425859 / 390625000000 : ℝ))
      (E := (cell12366 ⟨19, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (83418837144099 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (8964425859 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12367_0 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (84081164300169 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (573669670281 / 25000000000000 : ℝ))
      (E := (cell12367 ⟨0, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (84081164300169 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (573669670281 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_1 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (42023040255117 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (114734131661 / 5000000000000 : ℝ))
      (E := (cell12367 ⟨1, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (42023040255117 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (114734131661 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_2 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (84011021808677 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (286835830327 / 12500000000000 : ℝ))
      (E := (cell12367 ⟨2, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (84011021808677 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (286835830327 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_3 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (16795197631731 / 20000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294690661061 / 100000000000000 : ℝ))
      (E := (cell12367 ⟨3, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (16795197631731 / 20000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294690661061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_4 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (41970489761759 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147347319973 / 50000000000000 : ℝ))
      (E := (cell12367 ⟨4, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (41970489761759 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147347319973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_5 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (83905995866813 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (573674661523 / 25000000000000 : ℝ))
      (E := (cell12367 ⟨5, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (83905995866813 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (573674661523 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_6 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (41935518576139 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (573675657581 / 25000000000000 : ℝ))
      (E := (cell12367 ⟨6, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (41935518576139 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (573675657581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_7 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (523975645899 / 625000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294706601059 / 100000000000000 : ℝ))
      (E := (cell12367 ⟨7, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (523975645899 / 625000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294706601059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_8 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (41900597202809 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (458942124883 / 20000000000000 : ℝ))
      (E := (cell12367 ⟨8, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (41900597202809 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (458942124883 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_9 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (83766310301919 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (458942918479 / 20000000000000 : ℝ))
      (E := (cell12367 ⟨9, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (83766310301919 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (458942918479 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_10 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (83731450997237 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (573679657149 / 25000000000000 : ℝ))
      (E := (cell12367 ⟨10, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (83731450997237 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (573679657149 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_11 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (13391458633 / 16000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147361312211 / 50000000000000 : ℝ))
      (E := (cell12367 ⟨11, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (13391458633 / 16000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147361312211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_12 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (5228862915239 / 6250000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147363293473 / 50000000000000 : ℝ))
      (E := (cell12367 ⟨12, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (5228862915239 / 6250000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147363293473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_13 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (5226688845313 / 6250000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (143420661317 / 6250000000000 : ℝ))
      (E := (cell12367 ⟨13, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (5226688845313 / 6250000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (143420661317 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_14 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (83592261065031 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147367277673 / 50000000000000 : ℝ))
      (E := (cell12367 ⟨14, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (83592261065031 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147367277673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_15 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (16711505045861 / 20000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147369287111 / 50000000000000 : ℝ))
      (E := (cell12367 ⟨15, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (16711505045861 / 20000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147369287111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_16 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (83522813983423 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (22947425857 / 1000000000000 : ℝ))
      (E := (cell12367 ⟨16, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (83522813983423 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (22947425857 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_17 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (16697625458631 / 20000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294746537443 / 100000000000000 : ℝ))
      (E := (cell12367 ⟨17, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (16697625458631 / 20000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294746537443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_18 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (83453465124449 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147375275683 / 50000000000000 : ℝ))
      (E := (cell12367 ⟨18, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (83453465124449 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147375275683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_19 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (83418827443431 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (286844321833 / 12500000000000 : ℝ))
      (E := (cell12367 ⟨19, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (83418827443431 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (286844321833 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12368_0 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (42040574172677 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147270107409 / 50000000000000 : ℝ))
      (E := (cell12368 ⟨0, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (42040574172677 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147270107409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_1 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (16809212977777 / 20000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147272113841 / 50000000000000 : ℝ))
      (E := (cell12368 ⟨1, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (16809212977777 / 20000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147272113841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_2 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (84011006520321 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (573637060217 / 25000000000000 : ℝ))
      (E := (cell12368 ⟨2, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (84011006520321 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (573637060217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_3 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (83975973202819 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294552206051 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨3, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (83975973202819 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294552206051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_4 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (20985241224933 / 25000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294556190287 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨4, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (20985241224933 / 25000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294556190287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_5 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (5244123848413 / 6250000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (91782408103 / 4000000000000 : ℝ))
      (E := (cell12368 ⟨5, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (5244123848413 / 6250000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (91782408103 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_6 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (83871023191183 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147282096871 / 50000000000000 : ℝ))
      (E := (cell12368 ⟨6, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (83871023191183 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147282096871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_7 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (83836089713389 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294568172199 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨7, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (83836089713389 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294568172199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_8 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (83801181105343 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (573643051017 / 25000000000000 : ℝ))
      (E := (cell12368 ⟨8, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (83801181105343 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (573643051017 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_9 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (16753259466271 / 20000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294576181347 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨9, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (16753259466271 / 20000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294576181347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_10 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (41865719177959 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (18356641357 / 800000000000 : ℝ))
      (E := (cell12368 ⟨10, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (41865719177959 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (18356641357 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_11 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (83696604143713 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147292088149 / 50000000000000 : ℝ))
      (E := (cell12368 ⟨11, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (83696604143713 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147292088149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_12 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (41830897329803 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (458917630091 / 20000000000000 : ℝ))
      (E := (cell12368 ⟨12, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (41830897329803 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (458917630091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_13 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (41813504934323 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294592156999 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨13, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (41813504934323 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294592156999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_14 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (16718449947213 / 20000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294596144473 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨14, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (16718449947213 / 20000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294596144473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_15 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (20889378556819 / 25000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294600177329 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨15, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (20889378556819 / 25000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294600177329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_16 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (83522803307871 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294604145419 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨16, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (83522803307871 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294604145419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_17 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (83488116943621 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147304056341 / 50000000000000 : ℝ))
      (E := (cell12368 ⟨17, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (83488116943621 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147304056341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_18 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (41726727550239 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147306071451 / 50000000000000 : ℝ))
      (E := (cell12368 ⟨18, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (41726727550239 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147306071451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_19 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (16683763548913 / 20000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (17926688477 / 781250000000 : ℝ))
      (E := (cell12368 ⟨19, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (16683763548913 / 20000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (17926688477 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12369_0 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (42040566196561 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (573600464723 / 25000000000000 : ℝ))
      (E := (cell12369 ⟨0, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (42040566196561 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (573600464723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_1 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (42023024635039 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (17925045897 / 781250000000 : ℝ))
      (E := (cell12369 ⟨1, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (42023024635039 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (17925045897 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_2 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (16802198246893 / 20000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294409891857 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨2, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (16802198246893 / 20000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294409891857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_3 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (41987979124721 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294413861689 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨3, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (41987979124721 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294413861689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_4 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (20985237569591 / 25000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147208925683 / 50000000000000 : ℝ))
      (E := (cell12369 ⟨4, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (20985237569591 / 25000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147208925683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_5 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (83905967284777 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (35850341717 / 1562500000000 : ℝ))
      (E := (cell12369 ⟨5, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (83905967284777 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (35850341717 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_6 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (83871009232423 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294425868077 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨6, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (83871009232423 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294425868077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_7 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (8383607608523 / 10000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294429854347 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨7, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (8383607608523 / 10000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294429854347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_8 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (2095029195183 / 2500000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294433836853 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨8, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (2095029195183 / 2500000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294433836853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_9 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (83766284363 / 100000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147218911749 / 50000000000000 : ℝ))
      (E := (cell12369 ⟨9, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (83766284363 / 100000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147218911749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_10 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (2616607053649 / 3125000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (286805227741 / 12500000000000 : ℝ))
      (E := (cell12369 ⟨10, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (2616607053649 / 3125000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (286805227741 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_11 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (10462073979163 / 12500000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147222919769 / 50000000000000 : ℝ))
      (E := (cell12369 ⟨11, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (10462073979163 / 12500000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147222919769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_12 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (3346471307099 / 4000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294449825417 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨12, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (3346471307099 / 4000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294449825417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_13 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (83626998214331 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294453786387 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨13, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (83626998214331 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294453786387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_14 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (16718447681821 / 20000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147228893563 / 50000000000000 : ℝ))
      (E := (cell12369 ⟨14, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (16718447681821 / 20000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147228893563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_15 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (83557503227211 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147230887951 / 50000000000000 : ℝ))
      (E := (cell12369 ⟨15, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (83557503227211 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147230887951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_16 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (41761396317121 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294465758797 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨16, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (41761396317121 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294465758797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_17 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (83488106595971 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294469799817 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨17, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (83488106595971 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294469799817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_18 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (83453445078349 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147236894113 / 50000000000000 : ℝ))
      (E := (cell12369 ⟨18, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (83453445078349 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147236894113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_19 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (83418808047501 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147238893761 / 50000000000000 : ℝ))
      (E := (cell12369 ⟨19, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (83418808047501 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147238893761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12370_0 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (84081116443473 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (573565888893 / 25000000000000 : ℝ))
      (E := (cell12370 ⟨0, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (84081116443473 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (573565888893 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_1 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (84046033653811 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (71695861707 / 3125000000000 : ℝ))
      (E := (cell12370 ⟨1, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (84046033653811 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (71695861707 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_2 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (21002743987777 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147135797793 / 50000000000000 : ℝ))
      (E := (cell12370 ⟨2, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (21002743987777 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147135797793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_3 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (83975943298523 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (573568892533 / 25000000000000 : ℝ))
      (E := (cell12370 ⟨3, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (83975943298523 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (573568892533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_4 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (83940935659411 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294279565317 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨4, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (83940935659411 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294279565317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_5 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (41952976498661 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (458856706449 / 20000000000000 : ℝ))
      (E := (cell12370 ⟨5, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (41952976498661 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (458856706449 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_6 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (20967748818999 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294287537499 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨6, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (20967748818999 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294287537499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_7 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (20959015614841 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (286786441453 / 12500000000000 : ℝ))
      (E := (cell12370 ⟨7, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (20959015614841 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (286786441453 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_8 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (83801154511547 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (91771820911 / 4000000000000 : ℝ))
      (E := (cell12370 ⟨8, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (83801154511547 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (91771820911 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_9 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (10470783924607 / 12500000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (45885990377 / 2000000000000 : ℝ))
      (E := (cell12370 ⟨9, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (10470783924607 / 12500000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (45885990377 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_10 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (41865706539893 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147151763749 / 50000000000000 : ℝ))
      (E := (cell12370 ⟨10, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (41865706539893 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147151763749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_11 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (41848289762511 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147153749039 / 50000000000000 : ℝ))
      (E := (cell12370 ⟨11, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (41848289762511 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147153749039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_12 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (8366177069743 / 10000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294311495721 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨12, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (8366177069743 / 10000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294311495721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_13 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (41813493281031 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147157763659 / 50000000000000 : ℝ))
      (E := (cell12370 ⟨13, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (41813493281031 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147157763659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_14 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (1671844541683 / 2000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294319483307 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨14, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (1671844541683 / 2000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294319483307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_15 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (8355749222911 / 10000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (573580871549 / 25000000000000 : ℝ))
      (E := (cell12370 ⟨15, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (8355749222911 / 10000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (573580871549 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_16 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (83522781962537 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294327483983 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨16, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (83522781962537 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294327483983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_17 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (20872024062551 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147165741251 / 50000000000000 : ℝ))
      (E := (cell12370 ⟨17, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (20872024062551 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147165741251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_18 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (41726717529031 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (114716774367 / 5000000000000 : ℝ))
      (E := (cell12370 ⟨18, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (41726717529031 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (114716774367 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_19 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (83418798352239 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294339503843 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨19, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (83418798352239 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294339503843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12371_0 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (42040550248203 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (573531340659 / 25000000000000 : ℝ))
      (E := (cell12371 ⟨0, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (42040550248203 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (573531340659 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_1 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (16809203608017 / 20000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (458825865421 / 20000000000000 : ℝ))
      (E := (cell12371 ⟨1, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (16809203608017 / 20000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (458825865421 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_2 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (84010960670249 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (286766669007 / 12500000000000 : ℝ))
      (E := (cell12371 ⟨2, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (84010960670249 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (286766669007 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_3 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (4198796417503 / 5000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294137331383 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨3, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (4198796417503 / 5000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294137331383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_4 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (41970460521437 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294141332141 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨4, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (41970460521437 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294141332141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_5 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (83905938712241 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294145305433 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨5, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (83905938712241 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294145305433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_6 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (83870981321901 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (573537329461 / 25000000000000 : ℝ))
      (E := (cell12371 ⟨6, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (83870981321901 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (573537329461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_7 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (83836048835789 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (286769164989 / 12500000000000 : ℝ))
      (E := (cell12371 ⟨7, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (83836048835789 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (286769164989 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_8 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (3352045648721 / 4000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (458831463959 / 20000000000000 : ℝ))
      (E := (cell12371 ⟨8, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (3352045648721 / 4000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (458831463959 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_9 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (2094156460823 / 2500000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294161325391 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨9, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (2094156460823 / 2500000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294161325391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_10 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (41865700222487 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147082643167 / 50000000000000 : ℝ))
      (E := (cell12371 ⟨10, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (41865700222487 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147082643167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_11 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (20924141804717 / 25000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (143385579249 / 6250000000000 : ℝ))
      (E := (cell12371 ⟨11, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (20924141804717 / 25000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (143385579249 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_12 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (5228859919967 / 6250000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294173277479 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨12, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (5228859919967 / 6250000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294173277479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_13 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (83626974911837 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147088631817 / 50000000000000 : ℝ))
      (E := (cell12371 ⟨13, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (83626974911837 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147088631817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_14 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (83592215761199 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147090645561 / 50000000000000 : ℝ))
      (E := (cell12371 ⟨14, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (83592215761199 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147090645561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_15 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (83557481232973 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (458837050017 / 20000000000000 : ℝ))
      (E := (cell12371 ⟨15, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (83557481232973 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (458837050017 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_16 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (16704554258551 / 20000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (229418926283 / 10000000000000 : ℝ))
      (E := (cell12371 ⟨16, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (16704554258551 / 20000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (229418926283 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_17 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (41744042953159 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (71693539909 / 3125000000000 : ℝ))
      (E := (cell12371 ⟨17, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (41744042953159 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (71693539909 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_18 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (83453425039617 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (458839448049 / 20000000000000 : ℝ))
      (E := (cell12371 ⟨18, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (83453425039617 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (458839448049 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_19 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (41709394329389 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294201274019 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨19, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (41709394329389 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294201274019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12372_0 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (1051013556899 / 1250000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1146993582267 / 50000000000000 : ℝ))
      (E := (cell12372 ⟨0, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (1051013556899 / 1250000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1146993582267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_1 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (42023001214449 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1146995595031 / 50000000000000 : ℝ))
      (E := (cell12372 ⟨1, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (42023001214449 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1146995595031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_2 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (84010945391889 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2293995161267 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨2, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (84010945391889 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2293995161267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_3 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (16795182680811 / 20000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2293999145441 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨3, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (16795182680811 / 20000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2293999145441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_4 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (83940906428753 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147001575919 / 50000000000000 : ℝ))
      (E := (cell12372 ⟨4, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (83940906428753 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147001575919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_5 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (41952962214767 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294007131561 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨5, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (41952962214767 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294007131561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_6 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (4193548368507 / 5000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (286751393899 / 12500000000000 : ℝ))
      (E := (cell12372 ⟨6, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (4193548368507 / 5000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (286751393899 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_7 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (16767207042901 / 20000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (286751895159 / 12500000000000 : ℝ))
      (E := (cell12372 ⟨7, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (16767207042901 / 20000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (286751895159 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_8 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (2618785247711 / 3125000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294019111991 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨8, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (2618785247711 / 3125000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294019111991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_9 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (41883122735597 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294023127149 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨9, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (41883122735597 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294023127149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_10 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (10466423476541 / 12500000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (573506789113 / 25000000000000 : ℝ))
      (E := (cell12372 ⟨10, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (10466423476541 / 12500000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (573506789113 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_11 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (2092413872871 / 2500000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147015574629 / 50000000000000 : ℝ))
      (E := (cell12372 ⟨11, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (2092413872871 / 2500000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147015574629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_12 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (83661746743599 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294035112639 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨12, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (83661746743599 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294035112639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_13 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (41813481631829 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (458807822299 / 20000000000000 : ℝ))
      (E := (cell12372 ⟨13, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (41813481631829 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (458807822299 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_14 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (20898051110063 / 25000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (458808618873 / 20000000000000 : ℝ))
      (E := (cell12372 ⟨14, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (20898051110063 / 25000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (458808618873 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_15 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (83557470238799 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147023562849 / 50000000000000 : ℝ))
      (E := (cell12372 ⟨15, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (83557470238799 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147023562849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_16 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (16704552124979 / 20000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (114702554767 / 5000000000000 : ℝ))
      (E := (cell12372 ⟨16, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (16704552124979 / 20000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (114702554767 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_17 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (16697615112863 / 20000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147027533613 / 50000000000000 : ℝ))
      (E := (cell12372 ⟨17, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (16697615112863 / 20000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147027533613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_18 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (20863353755753 / 25000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294059105141 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨18, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (20863353755753 / 25000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294059105141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_19 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (83418778967117 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147031549027 / 50000000000000 : ℝ))
      (E := (cell12372 ⟨19, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (83418778967117 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147031549027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12373_0 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (16816213722003 / 20000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293849076819 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨0, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (16816213722003 / 20000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293849076819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_1 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (84045986820251 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (71682909553 / 3125000000000 : ℝ))
      (E := (cell12373 ⟨1, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (84045986820251 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (71682909553 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_2 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (42005465058013 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (458771416209 / 20000000000000 : ℝ))
      (E := (cell12373 ⟨2, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (42005465058013 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (458771416209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_3 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (16795179692101 / 20000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (458772214031 / 20000000000000 : ℝ))
      (E := (cell12373 ⟨3, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (16795179692101 / 20000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (458772214031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_4 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (41970445908523 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293865082281 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨4, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (41970445908523 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293865082281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_5 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (83905910149199 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (91754762741 / 4000000000000 : ℝ))
      (E := (cell12373 ⟨5, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (83905910149199 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (91754762741 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_6 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (8387095342071 / 10000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293873037549 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨6, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (8387095342071 / 10000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293873037549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_7 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (10479502699439 / 12500000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (458775411141 / 20000000000000 : ℝ))
      (E := (cell12373 ⟨7, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (10479502699439 / 12500000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (458775411141 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_8 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (83801114637729 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293881015289 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨8, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (83801114637729 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293881015289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_9 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (20941558127919 / 25000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293885040097 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨9, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (20941558127919 / 25000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293885040097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_10 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (1674627503637 / 2000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (573472255457 / 25000000000000 : ℝ))
      (E := (cell12373 ⟨10, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (1674627503637 / 2000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (573472255457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_11 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (41848271306469 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (458778605167 / 20000000000000 : ℝ))
      (E := (cell12373 ⟨11, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (41848271306469 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (458778605167 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_12 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (83661734769811 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (5734742503 / 250000000000 : ℝ))
      (E := (cell12373 ⟨12, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (83661734769811 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (5734742503 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_13 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (83626951617523 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (286737626603 / 12500000000000 : ℝ))
      (E := (cell12373 ⟨13, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (83626951617523 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (286737626603 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_14 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (83592193121309 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293905009243 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨14, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (83592193121309 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293905009243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_15 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (20889364811647 / 25000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293908996781 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨15, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (20889364811647 / 25000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293908996781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_16 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (83522749958957 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (286739122689 / 12500000000000 : ℝ))
      (E := (cell12373 ⟨16, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (83522749958957 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (286739122689 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_17 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (83488065224193 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293916969267 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨17, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (83488065224193 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293916969267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_18 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (83453405008249 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293920965631 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨18, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (83453405008249 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293920965631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_19 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (83418769277257 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1146962487973 / 50000000000000 : ℝ))
      (E := (cell12373 ⟨19, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (83418769277257 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1146962487973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12374_0 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (8408105267069 / 10000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146855520859 / 50000000000000 : ℝ))
      (E := (cell12374 ⟨0, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (8408105267069 / 10000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146855520859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_1 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (42022985607071 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (229371507401 / 10000000000000 : ℝ))
      (E := (cell12374 ⟨1, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (42022985607071 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (229371507401 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_2 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (4200545742133 / 5000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293719053569 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨2, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (4200545742133 / 5000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293719053569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_3 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (83975883519411 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146861523841 / 50000000000000 : ℝ))
      (E := (cell12374 ⟨3, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (83975883519411 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146861523841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_4 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (10492609650969 / 12500000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293727007733 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨4, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (10492609650969 / 12500000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293727007733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_5 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (41952947935619 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146865500269 / 50000000000000 : ℝ))
      (E := (cell12374 ⟨5, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (41952947935619 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146865500269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_6 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (83870939473611 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293735034833 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨6, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (83870939473611 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293735034833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_7 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (10479500997351 / 12500000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (458747800643 / 20000000000000 : ℝ))
      (E := (cell12374 ⟨7, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (10479500997351 / 12500000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (458747800643 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_8 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (16760220270191 / 20000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293743029691 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨8, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (16760220270191 / 20000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293743029691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_9 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (16753243910873 / 20000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146873503127 / 50000000000000 : ℝ))
      (E := (cell12374 ⟨9, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (16753243910873 / 20000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146873503127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_10 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (41865681276769 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293750998489 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨10, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (41865681276769 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293750998489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_11 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (41848265156581 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (286719376723 / 12500000000000 : ℝ))
      (E := (cell12374 ⟨11, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (41848265156581 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (286719376723 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_12 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (20915430699527 / 25000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293759001223 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨12, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (20915430699527 / 25000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293759001223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_13 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (83626939973431 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293762967623 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨13, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (83626939973431 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293762967623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_14 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (5224511362773 / 6250000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146883488829 / 50000000000000 : ℝ))
      (E := (cell12374 ⟨14, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (5224511362773 / 6250000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146883488829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_15 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (41778724128169 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293770979593 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨15, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (41778724128169 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293770979593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_16 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (4176136964747 / 5000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146887489751 / 50000000000000 : ℝ))
      (E := (cell12374 ⟨16, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (4176136964747 / 5000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146887489751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_17 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (83488054885951 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146889491607 / 50000000000000 : ℝ))
      (E := (cell12374 ⟨17, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (83488054885951 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146889491607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_18 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (41726697497663 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (573445734529 / 25000000000000 : ℝ))
      (E := (cell12374 ⟨18, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (41726697497663 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (573445734529 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_19 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (20854689897299 / 25000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146893482961 / 50000000000000 : ℝ))
      (E := (cell12374 ⟨19, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (20854689897299 / 25000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146893482961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

end BstLean.Part268
