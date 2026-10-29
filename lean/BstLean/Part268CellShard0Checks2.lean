import BstLean.Part268CellShard0Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12350_40 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (20674271338649 / 25000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297201782983 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨40, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (20674271338649 / 25000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297201782983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_41 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (1291608950159 / 1562500000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297205789441 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨41, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (1291608950159 / 1562500000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297205789441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_42 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (82628884028041 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (114860489563 / 5000000000000 : ℝ))
      (E := (cell12350 ⟨42, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (82628884028041 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (114860489563 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_43 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (20648704744557 / 25000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297213788181 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨43, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (20648704744557 / 25000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297213788181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_44 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (20640194407731 / 25000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297217779727 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨44, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (20640194407731 / 25000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297217779727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_45 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (82526759956467 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297221765199 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨45, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (82526759956467 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297221765199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_46 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (41246382962673 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148612871841 / 50000000000000 : ℝ))
      (E := (cell12350 ⟨46, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (41246382962673 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148612871841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_47 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (41229397754099 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (57430744323 / 2500000000000 : ℝ))
      (E := (cell12350 ⟨47, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (41229397754099 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (57430744323 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_48 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (2575776521119 / 3125000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297233733833 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨48, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (2575776521119 / 3125000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297233733833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_49 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (20597731349777 / 25000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148618871317 / 50000000000000 : ℝ))
      (E := (cell12350 ⟨49, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (20597731349777 / 25000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148618871317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_50 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (3294281025967 / 4000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148620869333 / 50000000000000 : ℝ))
      (E := (cell12350 ⟨50, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (3294281025967 / 4000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148620869333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_51 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (16464629879447 / 20000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148622859967 / 50000000000000 : ℝ))
      (E := (cell12350 ⟨51, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (16464629879447 / 20000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148622859967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_52 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (16457859322931 / 20000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297249743227 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨52, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (16457859322931 / 20000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297249743227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_53 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (41127733636473 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148626873589 / 50000000000000 : ℝ))
      (E := (cell12350 ⟨53, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (41127733636473 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148626873589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_54 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (16444332268753 / 20000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297257729153 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨54, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (16444332268753 / 20000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297257729153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_55 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (82187878798907 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297261745377 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨55, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (82187878798907 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297261745377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_56 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (82154119610311 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (114863286689 / 5000000000000 : ℝ))
      (E := (cell12350 ⟨56, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (82154119610311 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (114863286689 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_57 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (16424076750011 / 20000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297269750211 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨57, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (16424076750011 / 20000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297269750211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_58 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (41043335595179 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148636866067 / 50000000000000 : ℝ))
      (E := (cell12350 ⟨58, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (41043335595179 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148636866067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_59 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (10256622737947 / 12500000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297277735031 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨59, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (10256622737947 / 12500000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297277735031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12351_40 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (16539416472547 / 20000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297062226823 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨40, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (16539416472547 / 20000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297062226823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_41 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (41331485067139 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148533103567 / 50000000000000 : ℝ))
      (E := (cell12351 ⟨41, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (41331485067139 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148533103567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_42 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (8262888166767 / 10000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297070242277 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨42, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (8262888166767 / 10000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297070242277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_43 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (41297408466473 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (4594148429 / 200000000000 : ℝ))
      (E := (cell12351 ⟨43, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (41297408466473 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (4594148429 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_44 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (16512155180059 / 20000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297078182059 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨44, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (16512155180059 / 20000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297078182059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_45 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (82526758540057 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (459416440617 / 20000000000000 : ℝ))
      (E := (cell12351 ⟨45, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (82526758540057 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (459416440617 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_46 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (82492764822721 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297086217879 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨46, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (82492764822721 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297086217879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_47 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (20614698679731 / 25000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (574272556327 / 25000000000000 : ℝ))
      (E := (cell12351 ⟨47, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (20614698679731 / 25000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (574272556327 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_48 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (82424848199453 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (114854711201 / 5000000000000 : ℝ))
      (E := (cell12351 ⟨48, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (82424848199453 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (114854711201 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_49 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (82390925235239 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (574274553113 / 25000000000000 : ℝ))
      (E := (cell12351 ⟨49, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (82390925235239 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (574274553113 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_50 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (82357025797363 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297102188821 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨50, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (82357025797363 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297102188821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_51 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (10290393732131 / 12500000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (459421242021 / 20000000000000 : ℝ))
      (E := (cell12351 ⟨51, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (10290393732131 / 12500000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (459421242021 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_52 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (82289297385663 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (574277553793 / 25000000000000 : ℝ))
      (E := (cell12351 ⟨52, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (82289297385663 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (574277553793 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_53 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (41127734177361 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (179462047 / 7812500000 : ℝ))
      (E := (cell12351 ⟨53, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (41127734177361 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (179462047 / 7812500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_54 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (2055541568397 / 2500000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148559083379 / 50000000000000 : ℝ))
      (E := (cell12351 ⟨54, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (2055541568397 / 2500000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148559083379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_55 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (41093940250467 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (574280541717 / 25000000000000 : ℝ))
      (E := (cell12351 ⟨55, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (41093940250467 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (574280541717 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_56 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (82154121621823 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297126198949 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨56, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (82154121621823 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297126198949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_57 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (82120386070627 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148565100347 / 50000000000000 : ℝ))
      (E := (cell12351 ⟨57, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (82120386070627 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148565100347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_58 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (20521668454891 / 25000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148567084317 / 50000000000000 : ℝ))
      (E := (cell12351 ⟨58, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (20521668454891 / 25000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148567084317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_59 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (2564155776281 / 3125000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (35892784647 / 1562500000000 : ℝ))
      (E := (cell12351 ⟨59, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (2564155776281 / 3125000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (35892784647 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12352_40 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (82697079371843 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (287115340731 / 12500000000000 : ℝ))
      (E := (cell12352 ⟨40, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (82697079371843 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (287115340731 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_41 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (8266296745931 / 10000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296926738811 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨41, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (8266296745931 / 10000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296926738811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_42 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (20657219827047 / 25000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (35889542947 / 1562500000000 : ℝ))
      (E := (cell12352 ⟨42, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (20657219827047 / 25000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (35889542947 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_43 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (41297407444257 / 50000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (114846737749 / 5000000000000 : ℝ))
      (E := (cell12352 ⟨43, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (41297407444257 / 50000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (114846737749 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_44 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (41280387085239 / 50000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296938698639 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨44, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (41280387085239 / 50000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296938698639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_45 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (4126337856221 / 5000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (91877707859 / 4000000000000 : ℝ))
      (E := (cell12352 ⟨45, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (4126337856221 / 5000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (91877707859 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_46 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (82492763720829 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (459389349529 / 20000000000000 : ℝ))
      (E := (cell12352 ⟨46, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (82492763720829 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (459389349529 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_47 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (16491758786069 / 20000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296950733327 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨47, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (16491758786069 / 20000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296950733327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_48 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (82424847723753 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148477355501 / 50000000000000 : ℝ))
      (E := (cell12352 ⟨48, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (82424847723753 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148477355501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_49 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (82390925071987 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (574239684507 / 25000000000000 : ℝ))
      (E := (cell12352 ⟨49, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (82390925071987 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (574239684507 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_50 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (5147314121633 / 6250000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148481347399 / 50000000000000 : ℝ))
      (E := (cell12352 ⟨50, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (5147314121633 / 6250000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148481347399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_51 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (411615751587 / 500000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296966697189 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨51, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (411615751587 / 500000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296966697189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_52 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (82289298157173 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296970684069 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨52, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (82289298157173 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296970684069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_53 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (514096683981 / 625000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148487356017 / 50000000000000 : ℝ))
      (E := (cell12352 ⟨53, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (514096683981 / 625000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148487356017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_54 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (41110832064209 / 50000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (57424467987 / 2500000000000 : ℝ))
      (E := (cell12352 ⟨54, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (41110832064209 / 50000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (57424467987 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_55 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (16437576440669 / 20000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296982703563 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨55, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (16437576440669 / 20000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296982703563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_56 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (82154123633681 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296986720319 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨56, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (82154123633681 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296986720319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_57 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (41060194195753 / 50000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148495353721 / 50000000000000 : ℝ))
      (E := (cell12352 ⟨57, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (41060194195753 / 50000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148495353721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_58 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (82086676449039 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296994720597 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨58, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (82086676449039 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296994720597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_59 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (41026493889319 / 50000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (459399739403 / 20000000000000 : ℝ))
      (E := (cell12352 ⟨59, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (41026493889319 / 50000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (459399739403 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12353_40 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (516856727387 / 625000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (574195834693 / 25000000000000 : ℝ))
      (E := (cell12353 ⟨40, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (516856727387 / 625000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (574195834693 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_41 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (10332870598159 / 12500000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296787325739 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨41, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (10332870598159 / 12500000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296787325739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_42 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (82628876949597 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296791310253 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨42, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (82628876949597 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296791310253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_43 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (41297406422467 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296795292053 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨43, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (41297406422467 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296795292053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_44 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (82560772441473 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148399664733 / 50000000000000 : ℝ))
      (E := (cell12353 ⟨44, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (82560772441473 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148399664733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_45 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (16505351141911 / 20000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148401652101 / 50000000000000 : ℝ))
      (E := (cell12353 ⟨45, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (16505351141911 / 20000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148401652101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_46 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (82492762619671 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296807332979 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨46, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (82492762619671 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296807332979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_47 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (82458793142459 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296811296979 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨47, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (82458793142459 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296811296979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_48 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (20606211812177 / 25000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296815312581 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨48, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (20606211812177 / 25000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296815312581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_49 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (10298865613669 / 12500000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (574204829841 / 25000000000000 : ℝ))
      (E := (cell12353 ⟨49, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (10298865613669 / 12500000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (574204829841 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_50 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (8235702609547 / 10000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296823315547 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨50, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (8235702609547 / 10000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296823315547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_51 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (8232315077829 / 10000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296827299133 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨51, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (8232315077829 / 10000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296827299133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_52 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (41144649464591 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296831267911 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨52, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (41144649464591 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296831267911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_53 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (82255470519659 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296835278481 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨53, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (82255470519659 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296835278481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_54 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (82221665521379 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (459367853847 / 20000000000000 : ℝ))
      (E := (cell12353 ⟨54, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (82221665521379 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (459367853847 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_55 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (82187883906141 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296843296397 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨55, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (82187883906141 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296843296397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_56 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (16430825129177 / 20000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296847297891 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨56, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (16430825129177 / 20000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296847297891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_57 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (20530097678173 / 25000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (287106408807 / 12500000000000 : ℝ))
      (E := (cell12353 ⟨57, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (20530097678173 / 25000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (287106408807 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_58 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (41043339539391 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296855269753 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨58, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (41043339539391 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296855269753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_59 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (41026495358257 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (91874371687 / 4000000000000 : ℝ))
      (E := (cell12353 ⟨59, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (41026495358257 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (91874371687 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12354_40 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (16539414678593 / 20000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296643948173 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨40, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (16539414678593 / 20000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296643948173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_41 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (41331481056081 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (28708099599 / 1250000000000 : ℝ))
      (E := (cell12354 ⟨41, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (41331481056081 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (28708099599 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_42 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (16525774918379 / 20000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148325992987 / 50000000000000 : ℝ))
      (E := (cell12354 ⟨42, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (16525774918379 / 20000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148325992987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_43 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (82594810802203 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (574163985823 / 25000000000000 : ℝ))
      (E := (cell12354 ⟨43, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (82594810802203 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (574163985823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_44 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (41280385356639 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (574164989233 / 25000000000000 : ℝ))
      (E := (cell12354 ⟨44, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (41280385356639 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (574164989233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_45 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (41263377147731 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (574165991859 / 25000000000000 : ℝ))
      (E := (cell12354 ⟨45, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (41263377147731 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (574165991859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_46 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (16498552303849 / 20000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148333986943 / 50000000000000 : ℝ))
      (E := (cell12354 ⟨46, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (16498552303849 / 20000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148333986943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_47 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (20614698088817 / 25000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (287083996893 / 12500000000000 : ℝ))
      (E := (cell12354 ⟨47, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (20614698088817 / 25000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (287083996893 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_48 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (82424846774319 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296675969859 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨48, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (82424846774319 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296675969859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_49 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (20597731186833 / 25000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (143542497279 / 6250000000000 : ℝ))
      (E := (cell12354 ⟨49, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (20597731186833 / 25000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (143542497279 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_50 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (8235702624539 / 10000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148341966587 / 50000000000000 : ℝ))
      (E := (cell12354 ⟨50, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (8235702624539 / 10000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148341966587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_51 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (82323151239719 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (459337591393 / 20000000000000 : ℝ))
      (E := (cell12354 ⟨51, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (82323151239719 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (459337591393 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_52 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (8228929970169 / 10000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148345983351 / 50000000000000 : ℝ))
      (E := (cell12354 ⟨52, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (8228929970169 / 10000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148345983351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_53 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (82255471602819 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148347979981 / 50000000000000 : ℝ))
      (E := (cell12354 ⟨53, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (82255471602819 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148347979981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_54 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (41110833457381 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296699934113 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨54, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (41110833457381 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296699934113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_55 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (2054697140233 / 2500000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296703945373 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨55, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (2054697140233 / 2500000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296703945373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_56 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (41077063829217 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296707931669 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨56, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (41077063829217 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296707931669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_57 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (16424078606837 / 20000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (45934238977 / 2000000000000 : ℝ))
      (E := (cell12354 ⟨57, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (16424078606837 / 20000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (45934238977 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_58 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (41043340854397 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296715934377 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨58, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (41043340854397 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296715934377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_59 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (82052993654621 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296719943727 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨59, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (82052993654621 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296719943727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12355_40 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (82697070404979 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (91860186859 / 4000000000000 : ℝ))
      (E := (cell12355 ⟨40, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (82697070404979 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (91860186859 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_41 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (82662959439981 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (459301733071 / 20000000000000 : ℝ))
      (E := (cell12355 ⟨41, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (82662959439981 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (459301733071 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_42 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (41314436117541 / 50000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148256329127 / 50000000000000 : ℝ))
      (E := (cell12355 ⟨42, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (41314436117541 / 50000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148256329127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_43 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (82594808760323 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296516649911 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨43, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (82594808760323 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296516649911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_44 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (16512153797179 / 20000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (45930413973 / 2000000000000 : ℝ))
      (E := (cell12355 ⟨44, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (16512153797179 / 20000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (45930413973 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_45 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (82526752882141 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (114826234309 / 5000000000000 : ℝ))
      (E := (cell12355 ⟨45, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (82526752882141 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (114826234309 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_46 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (2577898763111 / 3125000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (459305734073 / 20000000000000 : ℝ))
      (E := (cell12355 ⟨46, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (2577898763111 / 3125000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (459305734073 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_47 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (8245879156877 / 10000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (574133162517 / 25000000000000 : ℝ))
      (E := (cell12355 ⟨47, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (8245879156877 / 10000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (574133162517 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_48 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (10303105787573 / 12500000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296536682837 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨48, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (10303105787573 / 12500000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296536682837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_49 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (82390924585929 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (91861625973 / 4000000000000 : ℝ))
      (E := (cell12355 ⟨49, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (82390924585929 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (91861625973 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_50 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (82357026395887 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (91861786623 / 4000000000000 : ℝ))
      (E := (cell12355 ⟨50, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (82357026395887 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (91861786623 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_51 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (41161575850843 / 50000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296548670687 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨51, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (41161575850843 / 50000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296548670687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_52 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (82289300474699 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296552662449 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨52, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (82289300474699 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296552662449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_53 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (82255472686439 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148278319221 / 50000000000000 : ℝ))
      (E := (cell12355 ⟨53, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (82255472686439 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148278319221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_54 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (82221668308567 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (229656065507 / 10000000000000 : ℝ))
      (E := (cell12355 ⟨54, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (82221668308567 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (229656065507 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_55 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (82187887312883 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (574141162623 / 25000000000000 : ℝ))
      (E := (cell12355 ⟨55, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (82187887312883 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (574141162623 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_56 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (2567316552229 / 3125000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296568680743 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨56, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (2567316552229 / 3125000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296568680743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_57 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (5132524709749 / 6250000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (459314536703 / 20000000000000 : ℝ))
      (E := (cell12355 ⟨57, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (5132524709749 / 6250000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (459314536703 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_58 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (41043342169537 / 50000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (574144163833 / 25000000000000 : ℝ))
      (E := (cell12355 ⟨58, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (41043342169537 / 50000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (574144163833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_59 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (82052996592957 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (91863226067 / 4000000000000 : ℝ))
      (E := (cell12355 ⟨59, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (82052996592957 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (91863226067 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12356_40 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (2067426685449 / 2500000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296365449969 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨40, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (2067426685449 / 2500000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296365449969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_41 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (82662956768729 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (114818473839 / 5000000000000 : ℝ))
      (E := (cell12356 ⟨41, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (82662956768729 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (114818473839 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_42 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (82628869879159 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296373444611 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨42, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (82628869879159 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296373444611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_43 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (82594806719293 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (459275494139 / 20000000000000 : ℝ))
      (E := (cell12356 ⟨43, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (82594806719293 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (459275494139 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_44 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (82560767259323 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148190718503 / 50000000000000 : ℝ))
      (E := (cell12356 ⟨44, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (82560767259323 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148190718503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_45 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (10315843933699 / 12500000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (143524091277 / 6250000000000 : ℝ))
      (E := (cell12356 ⟨45, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (10315843933699 / 12500000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (143524091277 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_46 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (5155797457537 / 6250000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296389481271 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨46, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (5155797457537 / 6250000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296389481271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_47 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (82458790782967 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (459278687901 / 20000000000000 : ℝ))
      (E := (cell12356 ⟨47, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (82458790782967 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (459278687901 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_48 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (5151552864219 / 6250000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148198725757 / 50000000000000 : ℝ))
      (E := (cell12356 ⟨48, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (5151552864219 / 6250000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148198725757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_49 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (82390924425141 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (3674242331 / 160000000000 : ℝ))
      (E := (cell12356 ⟨49, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (82390924425141 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (3674242331 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_50 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (82357026546961 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148202726901 / 50000000000000 : ℝ))
      (E := (cell12356 ⟨50, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (82357026546961 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148202726901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_51 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (2572598505131 / 3125000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148204720149 / 50000000000000 : ℝ))
      (E := (cell12356 ⟨51, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (2572598505131 / 3125000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148204720149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_52 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (41144650624103 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296413473147 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨52, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (41144650624103 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296413473147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_53 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (82255473770521 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296417431957 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨53, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (82255473770521 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296417431957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_54 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (16444333940559 / 20000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148210716053 / 50000000000000 : ℝ))
      (E := (cell12356 ⟨54, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (16444333940559 / 20000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148210716053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_55 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (82187889016829 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296425470821 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨55, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (82187889016829 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296425470821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_56 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (82154131684567 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296429426933 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨56, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (82154131684567 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296429426933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_57 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (8212039767809 / 10000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (459286683067 / 20000000000000 : ℝ))
      (E := (cell12356 ⟨57, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (8212039767809 / 10000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (459286683067 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_58 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (41043343484811 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (114821871631 / 5000000000000 : ℝ))
      (E := (cell12356 ⟨58, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (41043343484811 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (114821871631 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_59 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (20513249882881 / 25000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148220708009 / 50000000000000 : ℝ))
      (E := (cell12356 ⟨59, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (20513249882881 / 25000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148220708009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12357_40 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (82697064431909 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296226342367 / 100000000000000 : ℝ))
      (E := (cell12357 ⟨40, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (82697064431909 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296226342367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_41 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (16532590819681 / 20000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296230343461 / 100000000000000 : ℝ))
      (E := (cell12357 ⟨41, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (16532590819681 / 20000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296230343461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_42 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (661030940193 / 800000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (287029293131 / 12500000000000 : ℝ))
      (E := (cell12357 ⟨42, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (661030940193 / 800000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (287029293131 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_43 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (82594804679113 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (28702978601 / 1250000000000 : ℝ))
      (E := (cell12357 ⟨43, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (82594804679113 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (28702978601 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_44 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (82560765533561 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296242289617 / 100000000000000 : ℝ))
      (E := (cell12357 ⟨44, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (82560765533561 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296242289617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_45 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (41263375028907 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (574061572549 / 25000000000000 : ℝ))
      (E := (cell12357 ⟨45, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (41263375028907 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (574061572549 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_46 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (20623189555591 / 25000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148125144449 / 50000000000000 : ℝ))
      (E := (cell12357 ⟨46, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (20623189555591 / 25000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148125144449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_47 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (2576837187433 / 3125000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296254284581 / 100000000000000 : ℝ))
      (E := (cell12357 ⟨47, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (2576837187433 / 3125000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296254284581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_48 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (41212422677539 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148129137947 / 50000000000000 : ℝ))
      (E := (cell12357 ⟨48, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (41212422677539 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148129137947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_49 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (82390924264969 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (229626232019 / 10000000000000 : ℝ))
      (E := (cell12357 ⟨49, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (82390924264969 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (229626232019 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_50 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (82357026698611 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (114813314893 / 5000000000000 : ℝ))
      (E := (cell12357 ⟨50, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (82357026698611 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (114813314893 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_51 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (16464630525447 / 20000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (91850812991 / 4000000000000 : ℝ))
      (E := (cell12357 ⟨51, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (16464630525447 / 20000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (91850812991 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_52 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (82289302022213 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (574068570201 / 25000000000000 : ℝ))
      (E := (cell12357 ⟨52, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (82289302022213 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (574068570201 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_53 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (82255474855063 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (229627828149 / 10000000000000 : ℝ))
      (E := (cell12357 ⟨53, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (82255474855063 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (229627828149 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_54 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (20555417774361 / 25000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (574070581067 / 25000000000000 : ℝ))
      (E := (cell12357 ⟨54, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (20555417774361 / 25000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (574070581067 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_55 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (82187890721159 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296286288227 / 100000000000000 : ℝ))
      (E := (cell12357 ⟨55, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (82187890721159 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296286288227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_56 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (82154133698151 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (114814514421 / 5000000000000 : ℝ))
      (E := (cell12357 ⟨56, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (82154133698151 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (114814514421 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_57 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (82120400000503 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296294321651 / 100000000000000 : ℝ))
      (E := (cell12357 ⟨57, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (82120400000503 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296294321651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_58 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (82086689600439 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296298266241 / 100000000000000 : ℝ))
      (E := (cell12357 ⟨58, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (82086689600439 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296298266241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_59 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (1025662530879 / 1250000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296302295917 / 100000000000000 : ℝ))
      (E := (cell12357 ⟨59, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (1025662530879 / 1250000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296302295917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12358_40 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (3307882457873 / 4000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148043615623 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨40, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (3307882457873 / 4000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148043615623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_41 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (5166434464313 / 6250000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (11480456327 / 500000000000 : ℝ))
      (E := (cell12358 ⟨41, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (5166434464313 / 6250000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (11480456327 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_42 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (82628865169979 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296095242047 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨42, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (82628865169979 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296095242047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_43 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (41297401319891 / 50000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296099219633 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨43, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (41297401319891 / 50000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296099219633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_44 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (82560763808609 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (574025814121 / 25000000000000 : ℝ))
      (E := (cell12358 ⟨44, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (82560763808609 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (574025814121 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_45 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (82526748646807 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296107234303 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨45, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (82526748646807 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296107234303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_46 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (82492757124869 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296111210953 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨46, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (82492757124869 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296111210953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_47 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (41229394606719 / 50000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148057622087 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨47, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (41229394606719 / 50000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148057622087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_48 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (82424844883307 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296119214877 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨48, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (82424844883307 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296119214877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_49 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (20597731026353 / 25000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296123239271 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨49, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (20597731026353 / 25000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296123239271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_50 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (41178513425419 / 50000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (459225439549 / 20000000000000 : ℝ))
      (E := (cell12358 ⟨50, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (41178513425419 / 50000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (459225439549 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_51 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (321574816761 / 390625000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296131206171 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨51, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (321574816761 / 390625000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296131206171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_52 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (82289302796719 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (574033800853 / 25000000000000 : ℝ))
      (E := (cell12358 ⟨52, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (82289302796719 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (574033800853 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_53 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (16451095188013 / 20000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148069623031 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨53, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (16451095188013 / 20000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148069623031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_54 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (16444334498503 / 20000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296143213469 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨54, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (16444334498503 / 20000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296143213469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_55 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (5136743276617 / 6250000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (459229444169 / 20000000000000 : ℝ))
      (E := (cell12358 ⟨55, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (5136743276617 / 6250000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (459229444169 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_56 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (82154135712079 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296151206117 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨56, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (82154135712079 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296151206117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_57 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (41060201161611 / 50000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148077612563 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨57, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (41060201161611 / 50000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148077612563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_58 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (82086692231523 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296159215333 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨58, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (82086692231523 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296159215333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_59 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (41026502704673 / 50000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148081616107 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨59, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (41026502704673 / 50000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148081616107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12359_40 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (20674264615677 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295948234033 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨40, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (20674264615677 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295948234033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_41 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (82662948760539 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147976121299 / 50000000000000 : ℝ))
      (E := (cell12359 ⟨41, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (82662948760539 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147976121299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_42 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (41314431408361 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295956194367 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨42, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (41314431408361 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295956194367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_43 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (825948006013 / 1000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295960206573 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨43, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (825948006013 / 1000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295960206573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_44 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (20640190521117 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295964219993 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨44, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (20640190521117 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295964219993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_45 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (82526747236571 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (573992058481 / 25000000000000 : ℝ))
      (E := (cell12359 ⟨45, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (82526747236571 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (573992058481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_46 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (16498551205621 / 20000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295972188587 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨46, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (16498551205621 / 20000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295972188587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_47 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (82458788429713 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295976200531 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨47, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (82458788429713 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295976200531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_48 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (82424844412189 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (459196041913 / 20000000000000 : ℝ))
      (E := (cell12359 ⟨48, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (82424844412189 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (459196041913 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_49 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (8239092394647 / 10000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295984214121 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨49, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (8239092394647 / 10000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295984214121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_50 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (82357027003641 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (573997053103 / 25000000000000 : ℝ))
      (E := (cell12359 ⟨50, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (82357027003641 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (573997053103 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_51 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (41161576777467 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (459198440487 / 20000000000000 : ℝ))
      (E := (cell12359 ⟨51, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (41161576777467 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (459198440487 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_52 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (20572325892931 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147998090989 / 50000000000000 : ℝ))
      (E := (cell12359 ⟨52, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (20572325892931 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147998090989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_53 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (10281934628191 / 12500000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (574000051909 / 25000000000000 : ℝ))
      (E := (cell12359 ⟨53, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (10281934628191 / 12500000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (574000051909 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_54 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (10277709236001 / 12500000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (574001054449 / 25000000000000 : ℝ))
      (E := (cell12359 ⟨54, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (10277709236001 / 12500000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (574001054449 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_55 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (10273486766371 / 12500000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (574002052403 / 25000000000000 : ℝ))
      (E := (cell12359 ⟨55, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (10273486766371 / 12500000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (574002052403 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_56 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (82154137726353 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1148006090011 / 50000000000000 : ℝ))
      (E := (cell12359 ⟨56, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (82154137726353 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1148006090011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_57 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (82120404646247 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (18368129479 / 800000000000 : ℝ))
      (E := (cell12359 ⟨57, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (82120404646247 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (18368129479 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_58 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (656693558903 / 800000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1148010110381 / 50000000000000 : ℝ))
      (E := (cell12359 ⟨58, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (656693558903 / 800000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1148010110381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_59 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (82053008348601 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (229602422491 / 10000000000000 : ℝ))
      (E := (cell12359 ⟨59, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (82053008348601 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (229602422491 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12360_40 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (41348527739779 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147904646007 / 50000000000000 : ℝ))
      (E := (cell12360 ⟨40, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (41348527739779 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147904646007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_41 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (41331473046499 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147906637527 / 50000000000000 : ℝ))
      (E := (cell12360 ⟨41, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (41331473046499 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147906637527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_42 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (82628860464353 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295817260771 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨42, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (82628860464353 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295817260771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_43 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (82594798563667 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295821248899 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨43, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (82594798563667 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295821248899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_44 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (5160047522571 / 6250000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295825238953 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨44, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (5160047522571 / 6250000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295825238953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_45 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (16505349165421 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295829289059 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨45, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (16505349165421 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295829289059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_46 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (10311594366509 / 12500000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147916640327 / 50000000000000 : ℝ))
      (E := (cell12360 ⟨46, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (10311594366509 / 12500000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147916640327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_47 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (82458787646681 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147918635703 / 50000000000000 : ℝ))
      (E := (cell12360 ⟨47, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (82458787646681 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147918635703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_48 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (3296993757669 / 4000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147920629979 / 50000000000000 : ℝ))
      (E := (cell12360 ⟨48, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (3296993757669 / 4000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147920629979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_49 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (82390923788143 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295845244739 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨49, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (82390923788143 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295845244739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_50 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (82357027157021 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295849282909 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨50, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (82357027157021 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295849282909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_51 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (8232315401959 / 10000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147926627297 / 50000000000000 : ℝ))
      (E := (cell12360 ⟨51, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (8232315401959 / 10000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147926627297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_52 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (82289304347227 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295857275499 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨52, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (82289304347227 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295857275499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_53 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (1645109562229 / 2000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295861225231 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨53, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (1645109562229 / 2000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295861225231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_54 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (41110837641961 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295865278209 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨54, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (41110837641961 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295865278209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_55 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (82187895836447 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (91834770181 / 4000000000000 : ℝ))
      (E := (cell12360 ⟨55, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (82187895836447 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (91834770181 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_56 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (8215413974097 / 10000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (229587326923 / 10000000000000 : ℝ))
      (E := (cell12360 ⟨56, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (8215413974097 / 10000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (229587326923 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_57 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (41060203484789 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (229587726001 / 10000000000000 : ℝ))
      (E := (cell12360 ⟨57, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (41060203484789 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (229587726001 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_58 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (16417339498899 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (229588122339 / 10000000000000 : ℝ))
      (E := (cell12360 ⟨58, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (16417339498899 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (229588122339 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_59 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (16410602257617 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147942637003 / 50000000000000 : ℝ))
      (E := (cell12360 ⟨59, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (16410602257617 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147942637003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12361_40 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (41348526248687 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (1147835202597 / 50000000000000 : ℝ))
      (E := (cell12361 ⟨40, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (41348526248687 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (1147835202597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_41 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (5166433964149 / 6250000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (573918590693 / 25000000000000 : ℝ))
      (E := (cell12361 ⟨41, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (5166433964149 / 6250000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (573918590693 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_42 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (10328607264109 / 12500000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (918271353 / 40000000000 : ℝ))
      (E := (cell12361 ⟨42, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (10328607264109 / 12500000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (918271353 / 40000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_43 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (41297398263441 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (11478412027 / 500000000000 : ℝ))
      (E := (cell12361 ⟨43, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (41297398263441 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (11478412027 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_44 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (82560758638613 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (1147843186087 / 50000000000000 : ℝ))
      (E := (cell12361 ⟨44, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (82560758638613 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (1147843186087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_45 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (8252674441841 / 10000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (229569039971 / 10000000000000 : ℝ))
      (E := (cell12361 ⟨45, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (8252674441841 / 10000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (229569039971 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_46 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (82492753836771 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (1147847184723 / 50000000000000 : ℝ))
      (E := (cell12361 ⟨46, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (82492753836771 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (1147847184723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_47 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (82458786864341 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (1147849198963 / 50000000000000 : ℝ))
      (E := (cell12361 ⟨47, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (82458786864341 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (1147849198963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_48 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (41212421735957 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295702366059 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨48, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (41212421735957 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295702366059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_49 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (8239092363043 / 10000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (573926597513 / 25000000000000 : ℝ))
      (E := (cell12361 ⟨49, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (8239092363043 / 10000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (573926597513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_50 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (3294281092439 / 4000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (573927587573 / 25000000000000 : ℝ))
      (E := (cell12361 ⟨50, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (3294281092439 / 4000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (573927587573 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_51 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (82323154484783 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295714362649 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨51, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (82323154484783 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295714362649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_52 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (20572326280807 / 25000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (71741198937 / 3125000000000 : ℝ))
      (E := (cell12361 ⟨52, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (20572326280807 / 25000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (71741198937 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_53 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (10281934899729 / 12500000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295722357869 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨53, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (10281934899729 / 12500000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295722357869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_54 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (82221676680257 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (573931598677 / 25000000000000 : ℝ))
      (E := (cell12361 ⟨54, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (82221676680257 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (573931598677 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_55 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (20546974385577 / 25000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (573932588897 / 25000000000000 : ℝ))
      (E := (cell12361 ⟨55, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (20546974385577 / 25000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (573932588897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_56 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (20538535438983 / 25000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295734355559 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨56, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (20538535438983 / 25000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295734355559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_57 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (16424081858643 / 20000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295738391421 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨57, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (16424081858643 / 20000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295738391421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_58 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (41043350063191 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (1147871170747 / 50000000000000 : ℝ))
      (E := (cell12361 ⟨58, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (41043350063191 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (1147871170747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_59 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (82053014227799 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295746379503 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨59, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (82053014227799 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295746379503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12362_40 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (20674262379039 / 25000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (573882893393 / 25000000000000 : ℝ))
      (E := (cell12362 ⟨40, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (20674262379039 / 25000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (573882893393 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_41 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (10332867595087 / 12500000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295535564489 / 100000000000000 : ℝ))
      (E := (cell12362 ⟨41, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (10332867595087 / 12500000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295535564489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_42 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (41314427881139 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (459107911911 / 20000000000000 : ℝ))
      (E := (cell12362 ⟨42, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (41314427881139 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (459107911911 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_43 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (41297397245473 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (286942944813 / 12500000000000 : ℝ))
      (E := (cell12362 ⟨43, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (41297397245473 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (286942944813 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_44 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (825607569169 / 1000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147773780423 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨44, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (825607569169 / 1000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147773780423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_45 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (16505348602097 / 20000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147775782939 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨45, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (16505348602097 / 20000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147775782939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_46 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (82492752742201 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (35868055823 / 1562500000000 : ℝ))
      (E := (cell12362 ⟨46, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (82492752742201 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (35868055823 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_47 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (41229393041347 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (286944947511 / 12500000000000 : ℝ))
      (E := (cell12362 ⟨47, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (41229393041347 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (286944947511 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_48 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (82424843002757 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295563586767 / 100000000000000 : ℝ))
      (E := (cell12362 ⟨48, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (82424843002757 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295563586767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_49 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (20597730868333 / 25000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (229556753221 / 10000000000000 : ℝ))
      (E := (cell12362 ⟨49, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (20597730868333 / 25000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (229556753221 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_50 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (41178513732753 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295571532457 / 100000000000000 : ℝ))
      (E := (cell12362 ⟨50, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (41178513732753 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295571532457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_51 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (5145197184407 / 6250000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147787792787 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨51, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (5145197184407 / 6250000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147787792787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_52 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (5143081618733 / 6250000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (91823182857 / 4000000000000 : ℝ))
      (E := (cell12362 ⟨52, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (5143081618733 / 6250000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (91823182857 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_53 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (41127740142337 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (229558354653 / 10000000000000 : ℝ))
      (E := (cell12362 ⟨53, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (41127740142337 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (229558354653 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_54 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (82221678077013 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147793783647 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨54, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (82221678077013 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147793783647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_55 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (10273487406069 / 12500000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (573897892967 / 25000000000000 : ℝ))
      (E := (cell12362 ⟨55, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (10273487406069 / 12500000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (573897892967 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_56 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (41077071885619 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295595557191 / 100000000000000 : ℝ))
      (E := (cell12362 ⟨56, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (41077071885619 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295595557191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_57 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (82120411617157 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (573899894777 / 25000000000000 : ℝ))
      (E := (cell12362 ⟨57, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (82120411617157 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (573899894777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_58 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (10260837844817 / 12500000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147801787537 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨58, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (10260837844817 / 12500000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147801787537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_59 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (41026508583871 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295607541401 / 100000000000000 : ℝ))
      (E := (cell12362 ⟨59, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (41026508583871 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295607541401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12363_40 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (2584282704247 / 3125000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295392797149 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨40, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (2584282704247 / 3125000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295392797149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_41 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (16532587619187 / 20000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295396821469 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨41, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (16532587619187 / 20000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295396821469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_42 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (82628853412571 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295400791937 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨42, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (82628853412571 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295400791937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_43 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (41297396227929 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (286925603223 / 12500000000000 : ℝ))
      (E := (cell12363 ⟨43, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (41297396227929 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (286925603223 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_44 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (16512151039199 / 20000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (91816352199 / 4000000000000 : ℝ))
      (E := (cell12363 ⟨44, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (16512151039199 / 20000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (91816352199 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_45 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (8252674160333 / 10000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (573853196891 / 25000000000000 : ℝ))
      (E := (cell12363 ⟨45, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (8252674160333 / 10000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (573853196891 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_46 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (41246375824181 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295416831481 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨46, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (41246375824181 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295416831481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_47 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (41229392650869 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (286927602237 / 12500000000000 : ℝ))
      (E := (cell12363 ⟨47, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (41229392650869 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (286927602237 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_48 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (20606210633563 / 25000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (573856201071 / 25000000000000 : ℝ))
      (E := (cell12363 ⟨48, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (20606210633563 / 25000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (573856201071 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_49 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (5149432707303 / 6250000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147714394533 / 50000000000000 : ℝ))
      (E := (cell12363 ⟨49, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (5149432707303 / 6250000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147714394533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_50 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (20589256905153 / 25000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295432829407 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨50, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (20589256905153 / 25000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295432829407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_51 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (41161577708389 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147718402713 / 50000000000000 : ℝ))
      (E := (cell12363 ⟨51, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (41161577708389 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147718402713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_52 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (3291572267069 / 4000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295440832829 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨52, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (3291572267069 / 4000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295440832829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_53 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (3290219254879 / 4000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295444791217 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨53, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (3290219254879 / 4000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295444791217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_54 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (8222167947419 / 10000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (35866387437 / 1562500000000 : ℝ))
      (E := (cell12363 ⟨54, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (8222167947419 / 10000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (35866387437 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_55 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (82187900955179 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295452785231 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨55, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (82187900955179 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295452785231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_56 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (82154145786887 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295456815039 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨56, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (82154145786887 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295456815039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_57 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (16424082788281 / 20000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295460823073 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨57, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (16424082788281 / 20000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295460823073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_58 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (41043352695479 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295464805857 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨58, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (41043352695479 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295464805857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_59 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (82053020107913 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (143466801179 / 6250000000000 : ℝ))
      (E := (cell12363 ⟨59, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (82053020107913 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (143466801179 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12364_40 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (41348521778309 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295254134641 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨40, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (41348521778309 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295254134641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_41 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (826629354321 / 1000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (459051626743 / 20000000000000 : ℝ))
      (E := (cell12364 ⟨41, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (826629354321 / 1000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (459051626743 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_42 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (82628851063751 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (229526213841 / 10000000000000 : ℝ))
      (E := (cell12364 ⟨42, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (82628851063751 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (229526213841 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_43 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (41297395210809 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295266148457 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨43, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (41297395210809 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295266148457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_44 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (82560753475899 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (28690876307 / 1250000000000 : ℝ))
      (E := (cell12364 ⟨44, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (82560753475899 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (28690876307 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_45 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (16505348039389 / 20000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (1147637061801 / 50000000000000 : ℝ))
      (E := (cell12364 ⟨45, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (16505348039389 / 20000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (1147637061801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_46 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (41246375277627 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295278145873 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨46, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (41246375277627 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295278145873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_47 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (41229392260737 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (286910263919 / 12500000000000 : ℝ))
      (E := (cell12364 ⟨47, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (41229392260737 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (286910263919 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_48 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (82424842066401 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573821534103 / 25000000000000 : ℝ))
      (E := (cell12364 ⟨48, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (82424842066401 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573821534103 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_49 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (82390923160977 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (1147645050849 / 50000000000000 : ℝ))
      (E := (cell12364 ⟨49, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (82390923160977 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (1147645050849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_50 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (82357027776293 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (1147647061623 / 50000000000000 : ℝ))
      (E := (cell12364 ⟨50, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (82357027776293 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (1147647061623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_51 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (82323155883581 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295298140151 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨51, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (82323155883581 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295298140151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_52 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (82289307454221 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (1434563807 / 62500000000 : ℝ))
      (E := (cell12364 ⟨52, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (82289307454221 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (1434563807 / 62500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_53 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (16451096491947 / 20000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573826522983 / 25000000000000 : ℝ))
      (E := (cell12364 ⟨53, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (16451096491947 / 20000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573826522983 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_54 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (20555420217947 / 25000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (91812405591 / 4000000000000 : ℝ))
      (E := (cell12364 ⟨54, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (20555420217947 / 25000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (91812405591 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_55 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (82187902662187 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (286914264227 / 12500000000000 : ℝ))
      (E := (cell12364 ⟨55, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (82187902662187 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (286914264227 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_56 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (82154147802881 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295318129101 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨56, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (82154147802881 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295318129101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_57 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (41060208132979 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295322123317 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨57, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (41060208132979 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295322123317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_58 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (82086708023647 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (1147663046491 / 50000000000000 : ℝ))
      (E := (cell12364 ⟨58, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (82086708023647 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (1147663046491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_59 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (41026511524157 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (229533009357 / 10000000000000 : ℝ))
      (E := (cell12364 ⟨59, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (41026511524157 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (229533009357 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12365_40 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (10337130072287 / 12500000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (459023105467 / 20000000000000 : ℝ))
      (E := (cell12365 ⟨40, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (10337130072287 / 12500000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (459023105467 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_41 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (82662932769191 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147559750613 / 50000000000000 : ℝ))
      (E := (cell12365 ⟨41, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (82662932769191 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147559750613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_42 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (41314424357909 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295123540211 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨42, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (41314424357909 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295123540211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_43 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (3303791535529 / 4000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295127526523 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨43, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (3303791535529 / 4000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295127526523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_44 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (20640187939153 / 25000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295131518409 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨44, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (20640187939153 / 25000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295131518409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_45 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (82526738791329 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (57378387879 / 2500000000000 : ℝ))
      (E := (cell12365 ⟨45, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (82526738791329 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (57378387879 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_46 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (20623187365719 / 25000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295139515849 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨46, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (20623187365719 / 25000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295139515849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_47 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (82458783741901 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295143519333 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨47, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (82458783741901 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295143519333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_48 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (41212420799601 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295147524251 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨48, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (41212420799601 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295147524251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_49 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (82390923005721 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295151529027 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨49, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (82390923005721 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295151529027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_50 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (82357027932549 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295155531871 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨50, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (82357027932549 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295155531871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_51 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (2058078908773 / 2500000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295159530777 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨51, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (2058078908773 / 2500000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295159530777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_52 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (41144654116107 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (286895440441 / 12500000000000 : ℝ))
      (E := (cell12365 ⟨52, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (41144654116107 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (286895440441 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_53 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (41127741773977 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295167507693 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨53, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (41127741773977 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295167507693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_54 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (41110841134903 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (229517148063 / 10000000000000 : ℝ))
      (E := (cell12365 ⟨54, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (41110841134903 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (229517148063 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_55 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (82187904369577 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147587749277 / 50000000000000 : ℝ))
      (E := (cell12365 ⟨55, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (82187904369577 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147587749277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_56 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (41077074909609 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295179499381 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨56, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (41077074909609 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295179499381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_57 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (2566263080963 / 3125000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (14344896749 / 625000000000 : ℝ))
      (E := (cell12365 ⟨57, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (2566263080963 / 3125000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (14344896749 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_58 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (41043355328301 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147593747793 / 50000000000000 : ℝ))
      (E := (cell12365 ⟨58, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (41043355328301 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147593747793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_59 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (82053025988943 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147595741921 / 50000000000000 : ℝ))
      (E := (cell12365 ⟨59, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (82053025988943 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147595741921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12366_40 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (4134851880047 / 5000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (17929507619 / 781250000000 : ℝ))
      (E := (cell12366 ⟨40, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (4134851880047 / 5000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (17929507619 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_41 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (10332866263401 / 12500000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294980982741 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨41, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (10332866263401 / 12500000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294980982741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_42 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (20657211592193 / 25000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147492469291 / 50000000000000 : ℝ))
      (E := (cell12366 ⟨42, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (20657211592193 / 25000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147492469291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_43 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (516217414723 / 625000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294988959983 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨43, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (516217414723 / 625000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294988959983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_44 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (82560750038133 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (573748246929 / 25000000000000 : ℝ))
      (E := (cell12366 ⟨44, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (82560750038133 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (573748246929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_45 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (41263368693241 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294996962239 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨45, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (41263368693241 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294996962239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_46 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (20623187092807 / 25000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (229500094141 / 10000000000000 : ℝ))
      (E := (cell12366 ⟨46, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (20623187092807 / 25000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (229500094141 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_47 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (4122939148151 / 5000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (573751231021 / 25000000000000 : ℝ))
      (E := (cell12366 ⟨47, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (4122939148151 / 5000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (573751231021 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_48 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (16484968226531 / 20000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2295008967803 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨48, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (16484968226531 / 20000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2295008967803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_49 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (41195461425539 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2295012953207 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨49, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (41195461425539 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2295012953207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_50 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (82357028089379 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147508468693 / 50000000000000 : ℝ))
      (E := (cell12366 ⟨50, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (82357028089379 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147508468693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_51 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (16464631363759 / 20000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (459004195461 / 20000000000000 : ℝ))
      (E := (cell12366 ⟨51, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (16464631363759 / 20000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (459004195461 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_52 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (5143081813169 / 6250000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (286878119103 / 12500000000000 : ℝ))
      (E := (cell12366 ⟨52, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (5143081813169 / 6250000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (286878119103 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_53 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (10281935579579 / 12500000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147514460231 / 50000000000000 : ℝ))
      (E := (cell12366 ⟨53, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (10281935579579 / 12500000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147514460231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_54 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (20555420917061 / 25000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2295032936619 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨54, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (20555420917061 / 25000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2295032936619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_55 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (82187906077349 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147518469723 / 50000000000000 : ℝ))
      (E := (cell12366 ⟨55, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (82187906077349 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147518469723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_56 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (41077075917949 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147520462939 / 50000000000000 : ℝ))
      (E := (cell12366 ⟨56, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (41077075917949 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147520462939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_57 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (4106021045799 / 5000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (573761237939 / 25000000000000 : ℝ))
      (E := (cell12366 ⟨57, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (4106021045799 / 5000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (573761237939 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_58 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (2565209790307 / 3125000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147524477267 / 50000000000000 : ℝ))
      (E := (cell12366 ⟨58, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (2565209790307 / 3125000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147524477267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_59 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (410265144649 / 500000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (57376323263 / 2500000000000 : ℝ))
      (E := (cell12366 ⟨59, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (410265144649 / 500000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (57376323263 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12367_40 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (20674258656137 / 25000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147419239167 / 50000000000000 : ℝ))
      (E := (cell12367 ⟨40, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (20674258656137 / 25000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147419239167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_41 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (1653258548923 / 2000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (573710615197 / 25000000000000 : ℝ))
      (E := (cell12367 ⟨41, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (1653258548923 / 2000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (573710615197 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_42 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (82628844022611 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294846451047 / 100000000000000 : ℝ))
      (E := (cell12367 ⟨42, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (82628844022611 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294846451047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_43 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (82594784323981 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (57371261221 / 2500000000000 : ℝ))
      (E := (cell12367 ⟨43, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (82594784323981 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (57371261221 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_44 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (82560748320461 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (91794178147 / 4000000000000 : ℝ))
      (E := (cell12367 ⟨44, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (82560748320461 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (91794178147 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_45 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (20631683995601 / 25000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147429232421 / 50000000000000 : ℝ))
      (E := (cell12367 ⟨45, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (20631683995601 / 25000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147429232421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_46 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (82492747280309 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147431240707 / 50000000000000 : ℝ))
      (E := (cell12367 ⟨46, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (82492747280309 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147431240707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_47 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (82458782184829 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (458973288673 / 20000000000000 : ℝ))
      (E := (cell12367 ⟨47, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (82458782184829 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (458973288673 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_48 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (2060621016669 / 2500000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (573717616767 / 25000000000000 : ℝ))
      (E := (cell12367 ⟨48, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (2060621016669 / 2500000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (573717616767 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_49 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (10298865337131 / 12500000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (458974886633 / 20000000000000 : ℝ))
      (E := (cell12367 ⟨49, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (10298865337131 / 12500000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (458974886633 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_50 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (16471405649357 / 20000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294878457689 / 100000000000000 : ℝ))
      (E := (cell12367 ⟨50, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (16471405649357 / 20000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294878457689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_51 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (16464631457441 / 20000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294882479737 / 100000000000000 : ℝ))
      (E := (cell12367 ⟨51, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (16464631457441 / 20000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294882479737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_52 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (20572327447423 / 25000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294886438087 / 100000000000000 : ℝ))
      (E := (cell12367 ⟨52, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (20572327447423 / 25000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294886438087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_53 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (10281935715721 / 12500000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147445224141 / 50000000000000 : ℝ))
      (E := (cell12367 ⟨53, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (10281935715721 / 12500000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147445224141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_54 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (41110842533551 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147447224351 / 50000000000000 : ℝ))
      (E := (cell12367 ⟨54, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (41110842533551 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147447224351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_55 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (82187907785503 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147449218247 / 50000000000000 : ℝ))
      (E := (cell12367 ⟨55, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (82187907785503 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147449218247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_56 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (41077076926461 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294902467683 / 100000000000000 : ℝ))
      (E := (cell12367 ⟨56, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (41077076926461 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294902467683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_57 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (10265052905181 / 12500000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (573726619989 / 25000000000000 : ℝ))
      (E := (cell12367 ⟨57, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (10265052905181 / 12500000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (573726619989 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_58 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (82086715923313 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147455234913 / 50000000000000 : ℝ))
      (E := (cell12367 ⟨58, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (82086715923313 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147455234913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_59 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (41026515935443 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (458982886721 / 20000000000000 : ℝ))
      (E := (cell12367 ⟨59, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (41026515935443 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (458982886721 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12368_40 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (82697031649121 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294700036641 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨40, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (82697031649121 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294700036641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_41 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (82662924786017 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147352026421 / 50000000000000 : ℝ))
      (E := (cell12368 ⟨41, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (82662924786017 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147352026421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_42 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (10328605209667 / 12500000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294708077607 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨42, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (10328605209667 / 12500000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294708077607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_43 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (82594782293129 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147356025939 / 50000000000000 : ℝ))
      (E := (cell12368 ⟨43, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (82594782293129 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147356025939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_44 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (41280373301799 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147358016951 / 50000000000000 : ℝ))
      (E := (cell12368 ⟨44, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (41280373301799 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147358016951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_45 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (41263367289547 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (229472002297 / 10000000000000 : ℝ))
      (E := (cell12368 ⟨45, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (41263367289547 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (229472002297 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_46 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (82492746190121 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (45894480363 / 2000000000000 : ℝ))
      (E := (cell12368 ⟨46, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (82492746190121 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (45894480363 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_47 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (82458781407329 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294728018297 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨47, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (82458781407329 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294728018297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_48 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (82424840201517 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294732022049 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨48, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (82424840201517 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294732022049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_49 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (5149432658977 / 6250000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (91789441113 / 4000000000000 : ℝ))
      (E := (cell12368 ⟨49, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (5149432658977 / 6250000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (91789441113 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_50 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (20589257101191 / 25000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (573685008459 / 25000000000000 : ℝ))
      (E := (cell12368 ⟨50, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (20589257101191 / 25000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (573685008459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_51 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (10290394719519 / 12500000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (286843004759 / 12500000000000 : ℝ))
      (E := (cell12368 ⟨51, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (10290394719519 / 12500000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (286843004759 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_52 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (10286163821147 / 12500000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (573687009579 / 25000000000000 : ℝ))
      (E := (cell12368 ⟨52, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (10286163821147 / 12500000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (573687009579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_53 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (82255486815363 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (573688008033 / 25000000000000 : ℝ))
      (E := (cell12368 ⟨53, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (82255486815363 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (573688008033 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_54 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (82221686466381 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147378008439 / 50000000000000 : ℝ))
      (E := (cell12368 ⟨54, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (82221686466381 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147378008439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_55 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (82187909494039 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147380024383 / 50000000000000 : ℝ))
      (E := (cell12368 ⟨55, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (82187909494039 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147380024383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_56 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (5134634741893 / 6250000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (114738200331 / 5000000000000 : ℝ))
      (E := (cell12368 ⟨56, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (5134634741893 / 6250000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (114738200331 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_57 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (82120425567221 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294768005323 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨57, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (82120425567221 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294768005323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_58 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (20521679639267 / 25000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (458954408293 / 20000000000000 : ℝ))
      (E := (cell12368 ⟨58, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (20521679639267 / 25000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (458954408293 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_59 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (410265174061 / 500000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294776052261 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨59, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (410265174061 / 500000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294776052261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12369_40 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (82697028674657 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294561708871 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨40, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (82697028674657 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294561708871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_41 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (82662922126809 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294565700167 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨41, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (82662922126809 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294565700167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_42 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (82628839332947 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294569700739 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨42, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (82628839332947 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294569700739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_43 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (20648695065781 / 25000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (458914742063 / 20000000000000 : ℝ))
      (E := (cell12369 ⟨43, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (20648695065781 / 25000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (458914742063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_44 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (82560744887541 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294577669593 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨44, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (82560744887541 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294577669593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_45 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (82526733176553 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (458916339091 / 20000000000000 : ℝ))
      (E := (cell12369 ⟨45, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (82526733176553 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (458916339091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_46 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (41246372550331 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (229458566933 / 10000000000000 : ℝ))
      (E := (cell12369 ⟨46, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (41246372550331 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (229458566933 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_47 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (2061469515763 / 2500000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (28682371347 / 1250000000000 : ℝ))
      (E := (cell12369 ⟨47, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (2061469515763 / 2500000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (28682371347 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_48 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (41212419868463 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294593691647 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨48, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (41212419868463 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294593691647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_49 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (20597730597707 / 25000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147298839133 / 50000000000000 : ℝ))
      (E := (cell12369 ⟨49, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (20597730597707 / 25000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147298839133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_50 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (41178514281659 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (71706302057 / 3125000000000 : ℝ))
      (E := (cell12369 ⟨50, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (41178514281659 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (71706302057 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_51 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (82323158225633 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (458921130463 / 20000000000000 : ℝ))
      (E := (cell12369 ⟨51, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (82323158225633 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (458921130463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_52 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (41144655674579 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (143413105907 / 6250000000000 : ℝ))
      (E := (cell12369 ⟨52, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (41144655674579 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (143413105907 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_53 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (10281935988177 / 12500000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (458922734403 / 20000000000000 : ℝ))
      (E := (cell12369 ⟨53, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (10281935988177 / 12500000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (458922734403 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_54 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (82221687866079 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294617700193 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨54, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (82221687866079 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294617700193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_55 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (16437582240591 / 20000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294621658129 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨55, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (16437582240591 / 20000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294621658129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_56 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (41077078943999 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294625660867 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨56, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (41077078943999 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294625660867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_57 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (82120427893299 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294629646089 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨57, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (82120427893299 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294629646089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_58 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (8208672119109 / 10000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294633669449 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨58, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (8208672119109 / 10000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294633669449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_59 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (41026518876871 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (458927533633 / 20000000000000 : ℝ))
      (E := (cell12369 ⟨59, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (41026518876871 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (458927533633 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12370_40 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (82697025701157 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (458884675519 / 20000000000000 : ℝ))
      (E := (cell12370 ⟨40, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (82697025701157 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (458884675519 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_41 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (3306516778741 / 4000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (573606850691 / 25000000000000 : ℝ))
      (E := (cell12370 ⟨41, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (3306516778741 / 4000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (573606850691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_42 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (20657209247361 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294431379207 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨42, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (20657209247361 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294431379207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_43 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (16518955646793 / 20000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294435424151 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨43, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (16518955646793 / 20000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294435424151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_44 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (20640185793073 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (458887883911 / 20000000000000 : ℝ))
      (E := (cell12370 ⟨44, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (20640185793073 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (458887883911 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_45 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (4126336588739 / 5000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147221682317 / 50000000000000 : ℝ))
      (E := (cell12370 ⟨45, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (4126336588739 / 5000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147221682317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_46 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (20623186002983 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294447376101 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨46, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (20623186002983 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294447376101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_47 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (51536737409 / 62500000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294451393999 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨47, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (51536737409 / 62500000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294451393999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_48 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (41212419636493 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294455416963 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨48, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (41212419636493 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294455416963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_49 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (82390922238637 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294459384487 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨49, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (82390922238637 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294459384487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_50 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (16471405744489 / 20000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294463412607 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨50, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (16471405744489 / 20000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294463412607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_51 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (1646463173913 / 2000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294467381437 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨51, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (1646463173913 / 2000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294467381437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_52 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (20572328032409 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294471406679 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨52, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (20572328032409 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294471406679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_53 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (10281936124491 / 12500000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (229447536793 / 10000000000000 : ℝ))
      (E := (cell12370 ⟨53, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (10281936124491 / 12500000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (229447536793 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_54 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (20555422316549 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147239690281 / 50000000000000 : ℝ))
      (E := (cell12370 ⟨54, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (20555422316549 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147239690281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_55 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (82187912912253 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294483382719 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨55, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (82187912912253 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294483382719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_56 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (1643083198121 / 2000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147243685669 / 50000000000000 : ℝ))
      (E := (cell12370 ⟨56, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (1643083198121 / 2000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147243685669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_57 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (82120430219681 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (458898280451 / 20000000000000 : ℝ))
      (E := (cell12370 ⟨57, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (82120430219681 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (458898280451 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_58 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (41043361912689 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147247676891 / 50000000000000 : ℝ))
      (E := (cell12370 ⟨58, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (41043361912689 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147247676891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_59 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (10256630086939 / 12500000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294499399641 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨59, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (10256630086939 / 12500000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294499399641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12371_40 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (82697022728621 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294285160241 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨40, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (82697022728621 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294285160241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_41 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (41331458405583 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147144580317 / 50000000000000 : ℝ))
      (E := (cell12371 ⟨41, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (41331458405583 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147144580317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_42 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (3305153385873 / 4000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (91771726871 / 4000000000000 : ℝ))
      (E := (cell12371 ⟨42, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (3305153385873 / 4000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (91771726871 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_43 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (82594776205651 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294297193389 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨43, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (82594776205651 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294297193389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_44 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (82560741457849 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294301166173 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨44, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (82560741457849 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294301166173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_45 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (41263365186887 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (91772205927 / 4000000000000 : ℝ))
      (E := (cell12371 ⟨45, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (41263365186887 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (91772205927 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_46 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (8249274292393 / 10000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (71697160577 / 3125000000000 : ℝ))
      (E := (cell12371 ⟨46, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (8249274292393 / 10000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (71697160577 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_47 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (82458779078971 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (573578283973 / 25000000000000 : ℝ))
      (E := (cell12371 ⟨47, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (82458779078971 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (573578283973 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_48 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (41212419404849 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147158569547 / 50000000000000 : ℝ))
      (E := (cell12371 ⟨48, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (41212419404849 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147158569547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_49 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (41195461043529 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294321146489 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨49, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (41195461043529 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294321146489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_50 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (41178514441073 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (573581289071 / 25000000000000 : ℝ))
      (E := (cell12371 ⟨50, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (41178514441073 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (573581289071 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_51 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (41161579583101 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (573582291617 / 25000000000000 : ℝ))
      (E := (cell12371 ⟨51, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (41161579583101 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (573582291617 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_52 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (8228931291061 / 10000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147166587409 / 50000000000000 : ℝ))
      (E := (cell12371 ⟨52, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (8228931291061 / 10000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147166587409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_53 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (82255490086897 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294337178901 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨53, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (82255490086897 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294337178901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_54 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (82221690666733 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294341176071 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨54, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (82221690666733 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294341176071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_55 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (82187914621931 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (229434516347 / 10000000000000 : ℝ))
      (E := (cell12371 ⟨55, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (82187914621931 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (229434516347 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_56 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (16430832384889 / 20000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (229434913803 / 10000000000000 : ℝ))
      (E := (cell12371 ⟨56, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (16430832384889 / 20000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (229434913803 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_57 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (82120432546367 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (286794144449 / 12500000000000 : ℝ))
      (E := (cell12371 ⟨57, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (82120432546367 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (286794144449 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_58 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (82086726459931 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147178576801 / 50000000000000 : ℝ))
      (E := (cell12371 ⟨58, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (82086726459931 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147178576801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_59 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (8205304363751 / 10000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294361128367 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨59, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (8205304363751 / 10000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294361128367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12372_40 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (10337127469631 / 12500000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294146998099 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨40, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (10337127469631 / 12500000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294146998099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_41 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (8266291415473 / 10000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147075516259 / 50000000000000 : ℝ))
      (E := (cell12372 ⟨41, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (8266291415473 / 10000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147075516259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_42 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (82628832305091 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (14338468873 / 625000000000 : ℝ))
      (E := (cell12372 ⟨42, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (82628832305091 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (14338468873 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_43 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (10324346772273 / 12500000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294159018027 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨43, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (10324346772273 / 12500000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294159018027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_44 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (41280369872107 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (286770378383 / 12500000000000 : ℝ))
      (E := (cell12372 ⟨44, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (41280369872107 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (286770378383 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_45 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (2578960280423 / 3125000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (573541746811 / 25000000000000 : ℝ))
      (E := (cell12372 ⟨45, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (2578960280423 / 3125000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (573541746811 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_46 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (41246370918329 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147085507637 / 50000000000000 : ℝ))
      (E := (cell12372 ⟨46, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (41246370918329 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147085507637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_47 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (10307347288029 / 12500000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (7169296851 / 312500000000 : ℝ))
      (E := (cell12372 ⟨47, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (10307347288029 / 12500000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (7169296851 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_48 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (4121241917353 / 5000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294178975847 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨48, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (4121241917353 / 5000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294178975847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_49 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (82390921936091 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (91767318571 / 4000000000000 : ℝ))
      (E := (cell12372 ⟨49, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (82390921936091 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (91767318571 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_50 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (82357029042421 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294187014757 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨50, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (82357029042421 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294187014757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_51 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (82323159637289 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294191007407 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨51, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (82323159637289 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294191007407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_52 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (82289313692081 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (143387187433 / 6250000000000 : ℝ))
      (E := (cell12372 ⟨52, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (82289313692081 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (143387187433 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_53 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (20563872794581 / 25000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147099493443 / 50000000000000 : ℝ))
      (E := (cell12372 ⟨53, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (20563872794581 / 25000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147099493443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_54 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (82221692067689 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (458840593727 / 20000000000000 : ℝ))
      (E := (cell12372 ⟨54, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (82221692067689 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (458840593727 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_55 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (82187916331991 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294207000381 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨55, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (82187916331991 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294207000381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_56 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (41077081971591 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (573552740237 / 25000000000000 : ℝ))
      (E := (cell12372 ⟨56, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (41077081971591 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (573552740237 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_57 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (82120434873357 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294214965217 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨57, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (82120434873357 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294214965217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_58 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (328346916379 / 400000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294219009773 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨58, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (328346916379 / 400000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294219009773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_59 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (16410609315947 / 20000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (573555743167 / 25000000000000 : ℝ))
      (E := (cell12372 ⟨59, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (16410609315947 / 20000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (573555743167 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12373_40 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (41348508393219 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (71687777849 / 3125000000000 : ℝ))
      (E := (cell12373 ⟨40, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (41348508393219 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (71687777849 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_41 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (41331455749609 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147006450469 / 50000000000000 : ℝ))
      (E := (cell12373 ⟨41, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (41331455749609 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147006450469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_42 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (82628829964241 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147008461463 / 50000000000000 : ℝ))
      (E := (cell12373 ⟨42, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (82628829964241 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147008461463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_43 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (82594772151561 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (229402089807 / 10000000000000 : ℝ))
      (E := (cell12373 ⟨43, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (82594772151561 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (229402089807 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_44 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (10320092253923 / 12500000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147012442307 / 50000000000000 : ℝ))
      (E := (cell12373 ⟨44, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (10320092253923 / 12500000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147012442307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_45 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (41263363787033 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147014440921 / 50000000000000 : ℝ))
      (E := (cell12373 ⟨45, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (41263363787033 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147014440921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_46 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (41246370375057 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147016444411 / 50000000000000 : ℝ))
      (E := (cell12373 ⟨46, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (41246370375057 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147016444411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_47 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (41229388765091 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (458807380881 / 20000000000000 : ℝ))
      (E := (cell12373 ⟨47, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (41229388765091 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (458807380881 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_48 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (82424837885073 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2294040868321 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨48, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (82424837885073 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2294040868321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_49 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (82390921785737 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2294044896769 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨49, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (82390921785737 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2294044896769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_50 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (82357029203269 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147024435063 / 50000000000000 : ℝ))
      (E := (cell12373 ⟨50, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (82357029203269 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147024435063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_51 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (8232316010891 / 10000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2294052904257 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨51, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (8232316010891 / 10000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2294052904257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_52 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (82289314474047 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (573514219753 / 25000000000000 : ℝ))
      (E := (cell12373 ⟨52, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (82289314474047 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (573514219753 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_53 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (642621033361 / 781250000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2294060909929 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨53, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (642621033361 / 781250000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2294060909929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_54 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (10277711683633 / 12500000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147032438171 / 50000000000000 : ℝ))
      (E := (cell12373 ⟨54, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (10277711683633 / 12500000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147032438171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_55 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (82187918042431 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (458813778691 / 20000000000000 : ℝ))
      (E := (cell12373 ⟨55, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (82187918042431 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (458813778691 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_56 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (82154165962261 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147036449591 / 50000000000000 : ℝ))
      (E := (cell12373 ⟨56, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (82154165962261 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147036449591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_57 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (82120437200651 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (573519222561 / 25000000000000 : ℝ))
      (E := (cell12373 ⟨57, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (82120437200651 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (573519222561 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_58 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (20521682932459 / 25000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147040431577 / 50000000000000 : ℝ))
      (E := (cell12373 ⟨58, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (20521682932459 / 25000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147040431577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_59 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (20513262380547 / 25000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2294084873381 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨59, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (20513262380547 / 25000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2294084873381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12374_40 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (8269701381679 / 10000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293870898167 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨40, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (8269701381679 / 10000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293870898167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_41 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (8266290884463 / 10000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146937441687 / 50000000000000 : ℝ))
      (E := (cell12374 ⟨41, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (8266290884463 / 10000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146937441687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_42 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (20657206906069 / 25000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (286734860189 / 12500000000000 : ℝ))
      (E := (cell12374 ⟨42, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (20657206906069 / 25000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (286734860189 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_43 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (10324346265723 / 12500000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146941446151 / 50000000000000 : ℝ))
      (E := (cell12374 ⟨43, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (10324346265723 / 12500000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146941446151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_44 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (129001150499 / 156250000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293886856441 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨44, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (129001150499 / 156250000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293886856441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_45 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (82526726175363 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (458778178161 / 20000000000000 : ℝ))
      (E := (cell12374 ⟨45, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (82526726175363 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (458778178161 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_46 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (41246369832149 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293894876823 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨46, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (41246369832149 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293894876823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_47 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (82458776756821 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (45877977443 / 2000000000000 : ℝ))
      (E := (cell12374 ⟨47, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (82458776756821 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (45877977443 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_48 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (10303104677967 / 12500000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (114695143771 / 5000000000000 : ℝ))
      (E := (cell12374 ⟨48, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (10303104677967 / 12500000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (114695143771 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_49 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (41195460817997 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293906885051 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨49, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (41195460817997 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293906885051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_50 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (8235702936469 / 10000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (458782168059 / 20000000000000 : ℝ))
      (E := (cell12374 ⟨50, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (8235702936469 / 10000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (458782168059 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_51 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (41161580290533 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146957428509 / 50000000000000 : ℝ))
      (E := (cell12374 ⟨51, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (41161580290533 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146957428509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_52 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (8228931525651 / 10000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (573479718517 / 25000000000000 : ℝ))
      (E := (cell12374 ⟨52, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (8228931525651 / 10000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (573479718517 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_53 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (82255493362549 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (229392282999 / 10000000000000 : ℝ))
      (E := (cell12374 ⟨53, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (82255493362549 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (229392282999 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_54 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (41110847435429 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (45878536803 / 2000000000000 : ℝ))
      (E := (cell12374 ⟨54, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (41110847435429 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (45878536803 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_55 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (82187919753251 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146965421347 / 50000000000000 : ℝ))
      (E := (cell12374 ⟨55, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (82187919753251 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146965421347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_56 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (41077083990841 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293934834553 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨56, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (41077083990841 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293934834553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_57 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (82120439528249 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146969435781 / 50000000000000 : ℝ))
      (E := (cell12374 ⟨57, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (82120439528249 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146969435781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_58 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (41043367182593 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293942832029 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨58, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (41043367182593 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293942832029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_59 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (20513263116217 / 25000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293946830511 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨59, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (20513263116217 / 25000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293946830511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

end BstLean.Part268
