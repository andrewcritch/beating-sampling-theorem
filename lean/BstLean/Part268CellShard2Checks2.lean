import BstLean.Part268CellShard2Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12400_40 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (16539387388571 / 20000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (229030404937 / 10000000000000 : ℝ))
      (E := (cell12400 ⟨40, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (16539387388571 / 20000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (229030404937 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_41 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (82662840148497 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145154003167 / 50000000000000 : ℝ))
      (E := (cell12400 ⟨41, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (82662840148497 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145154003167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_42 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (82628767094631 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290312053951 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨42, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (82628767094631 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290312053951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_43 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (82594717751333 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (229031601563 / 10000000000000 : ℝ))
      (E := (cell12400 ⟨43, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (82594717751333 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (229031601563 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_44 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (8256069208883 / 10000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290320008337 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨44, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (8256069208883 / 10000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290320008337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_45 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (33010676031 / 40000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145162015669 / 50000000000000 : ℝ))
      (E := (cell12400 ⟨45, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (33010676031 / 40000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145162015669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_46 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (8249271168787 / 10000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145164012411 / 50000000000000 : ℝ))
      (E := (cell12400 ⟨46, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (8249271168787 / 10000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145164012411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_47 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (82458756890617 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (572583011607 / 25000000000000 : ℝ))
      (E := (cell12400 ⟨47, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (82458756890617 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (572583011607 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_48 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (41212412828281 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290336035867 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨48, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (41212412828281 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290336035867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_49 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (41195458978339 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145170025197 / 50000000000000 : ℝ))
      (E := (cell12400 ⟨49, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (41195458978339 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145170025197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_50 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (41178516881039 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290344029243 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨50, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (41178516881039 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290344029243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_51 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (41161586522013 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290348029287 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨51, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (41161586522013 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290348029287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_52 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (82289335773927 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (458070409657 / 20000000000000 : ℝ))
      (E := (cell12400 ⟨52, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (82289335773927 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (458070409657 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_53 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (82255521923329 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145178012379 / 50000000000000 : ℝ))
      (E := (cell12400 ⟨53, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (82255521923329 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145178012379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_54 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (20555432865981 / 25000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (286295001877 / 12500000000000 : ℝ))
      (E := (cell12400 ⟨54, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (20555432865981 / 25000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (286295001877 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_55 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (82187964367547 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (114518200809 / 5000000000000 : ℝ))
      (E := (cell12400 ⟨55, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (82187964367547 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (114518200809 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_56 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (8215422060617 / 10000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (458073605033 / 20000000000000 : ℝ))
      (E := (cell12400 ⟨56, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (8215422060617 / 10000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (458073605033 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_57 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (8212050015191 / 10000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145186019337 / 50000000000000 : ℝ))
      (E := (cell12400 ⟨57, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (8212050015191 / 10000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145186019337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_58 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (4104340148851 / 5000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290376053201 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨58, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (4104340148851 / 5000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290376053201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_59 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (20513282263473 / 25000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290380005871 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨59, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (20513282263473 / 25000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290380005871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12401_40 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (82696933999087 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (91606706601 / 4000000000000 : ℝ))
      (E := (cell12401 ⟨40, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (82696933999087 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (91606706601 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_41 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (20665709379683 / 25000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290171657933 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨41, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (20665709379683 / 25000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290171657933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_42 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (16525752955687 / 20000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (1145087841743 / 50000000000000 : ℝ))
      (E := (cell12401 ⟨42, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (16525752955687 / 20000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (1145087841743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_43 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (5162169734267 / 6250000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290179682599 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨43, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (5162169734267 / 6250000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290179682599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_44 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (10320086299809 / 12500000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572545913671 / 25000000000000 : ℝ))
      (E := (cell12401 ⟨44, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (10320086299809 / 12500000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572545913671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_45 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (82526688699413 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290187657771 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨45, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (82526688699413 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290187657771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_46 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (82492710621623 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (458038338181 / 20000000000000 : ℝ))
      (E := (cell12401 ⟨46, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (82492710621623 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (458038338181 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_47 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (41229378067889 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (458039138807 / 20000000000000 : ℝ))
      (E := (cell12401 ⟨47, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (41229378067889 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (458039138807 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_48 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (82424825212703 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290199665703 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨48, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (82424825212703 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290199665703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_49 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (82390917823369 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572550915791 / 25000000000000 : ℝ))
      (E := (cell12401 ⟨49, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (82390917823369 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572550915791 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_50 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (20589258484723 / 25000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290207684603 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨50, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (20589258484723 / 25000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290207684603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_51 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (41161586765267 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (1145105834507 / 50000000000000 : ℝ))
      (E := (cell12401 ⟨51, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (41161586765267 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (1145105834507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_52 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (82289336569703 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (57255391827 / 2500000000000 : ℝ))
      (E := (cell12401 ⟨52, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (82289336569703 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (57255391827 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_53 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (82255523027947 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290219694347 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨53, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (82255523027947 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290219694347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_54 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (82221732876959 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (22902236711 / 1000000000000 : ℝ))
      (E := (cell12401 ⟨54, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (82221732876959 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (22902236711 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_55 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (41093983044287 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290227659461 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨55, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (41093983044287 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290227659461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_56 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (41077111317383 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290231656343 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨56, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (41077111317383 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290231656343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_57 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (82120502487651 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (143139728653 / 6250000000000 : ℝ))
      (E := (cell12401 ⟨57, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (82120502487651 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (143139728653 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_58 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (20521701404871 / 25000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (229023966227 / 10000000000000 : ℝ))
      (E := (cell12401 ⟨58, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (20521701404871 / 25000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (229023966227 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_59 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (41026566001329 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (1145121832049 / 50000000000000 : ℝ))
      (E := (cell12401 ⟨59, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (41026566001329 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (1145121832049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12402_40 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (82696931056273 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (458006278929 / 20000000000000 : ℝ))
      (E := (cell12402 ⟨40, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (82696931056273 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (458006278929 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_41 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (82662834889883 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1145017682421 / 50000000000000 : ℝ))
      (E := (cell12402 ⟨41, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (82662834889883 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1145017682421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_42 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (20657190615779 / 25000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1145019684197 / 50000000000000 : ℝ))
      (E := (cell12402 ⟨42, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (20657190615779 / 25000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1145019684197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_43 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (1651894274921 / 2000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (572510851251 / 25000000000000 : ℝ))
      (E := (cell12402 ⟨43, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (1651894274921 / 2000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (572510851251 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_44 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (82560688708913 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290047356531 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨44, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (82560688708913 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290047356531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_45 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (41263343661043 / 50000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1145025699301 / 50000000000000 : ℝ))
      (E := (cell12402 ⟨45, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (41263343661043 / 50000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1145025699301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_46 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (82492709556097 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1145027676879 / 50000000000000 : ℝ))
      (E := (cell12402 ⟨46, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (82492709556097 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1145027676879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_47 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (82458755381623 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (572514849333 / 25000000000000 : ℝ))
      (E := (cell12402 ⟨47, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (82458755381623 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (572514849333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_48 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (5151551548093 / 6250000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (572515837823 / 25000000000000 : ℝ))
      (E := (cell12402 ⟨48, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (5151551548093 / 6250000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (572515837823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_49 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (16478183538133 / 20000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290067390681 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨49, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (16478183538133 / 20000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290067390681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_50 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (5147314632267 / 6250000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (458014279169 / 20000000000000 : ℝ))
      (E := (cell12402 ⟨50, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (5147314632267 / 6250000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (458014279169 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_51 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (82323174017571 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290075364683 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨51, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (82323174017571 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290075364683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_52 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (82289337365969 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290079353881 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨52, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (82289337365969 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290079353881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_53 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (82255524133017 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290083360981 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨53, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (82255524133017 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290083360981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_54 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (10277716786301 / 12500000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (572521845829 / 25000000000000 : ℝ))
      (E := (cell12402 ⟨54, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (10277716786301 / 12500000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (572521845829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_55 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (10273495976247 / 12500000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290091358937 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨55, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (10273495976247 / 12500000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290091358937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_56 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (82154224663699 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (286261925359 / 12500000000000 : ℝ))
      (E := (cell12402 ⟨56, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (82154224663699 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (286261925359 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_57 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (20530126205923 / 25000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290099393659 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨57, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (20530126205923 / 25000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290099393659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_58 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (8208680826221 / 10000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1145051693431 / 50000000000000 : ℝ))
      (E := (cell12402 ⟨58, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (8208680826221 / 10000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1145051693431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_59 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (82053134951647 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290107378769 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨59, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (82053134951647 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290107378769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12403_40 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (82696928114413 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (457979035903 / 20000000000000 : ℝ))
      (E := (cell12403 ⟨40, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (82696928114413 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (457979035903 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_41 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (20665708065487 / 25000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (457979825413 / 20000000000000 : ℝ))
      (E := (cell12403 ⟨41, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (20665708065487 / 25000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (457979825413 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_42 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (82628760148673 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (572475791861 / 25000000000000 : ℝ))
      (E := (cell12403 ⟨42, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (82628760148673 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (572475791861 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_43 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (10324338968083 / 12500000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289907124063 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨43, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (10324338968083 / 12500000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289907124063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_44 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (82560687020153 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289911172693 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨44, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (82560687020153 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289911172693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_45 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (82526685945519 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (457983027233 / 20000000000000 : ℝ))
      (E := (cell12403 ⟨45, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (82526685945519 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (457983027233 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_46 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (20623177122823 / 25000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289919131099 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨46, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (20623177122823 / 25000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289919131099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_47 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (82458754628149 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289923156323 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨47, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (82458754628149 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289923156323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_48 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (82424824326917 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (286240893943 / 12500000000000 : ℝ))
      (E := (cell12403 ⟨48, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (82424824326917 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (286240893943 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_49 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (10298864694821 / 12500000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (457986223017 / 20000000000000 : ℝ))
      (E := (cell12403 ⟨49, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (10298864694821 / 12500000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (457986223017 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_50 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (82357034294219 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (286241895371 / 12500000000000 : ℝ))
      (E := (cell12403 ⟨50, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (82357034294219 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (286241895371 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_51 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (5145198406571 / 6250000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289939116297 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨51, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (5145198406571 / 6250000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289939116297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_52 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (3291573526509 / 4000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289943149689 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨52, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (3291573526509 / 4000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289943149689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_53 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (82255525238539 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289947142709 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨53, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (82255525238539 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289947142709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_54 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (8222173570427 / 10000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (457990230333 / 20000000000000 : ℝ))
      (E := (cell12403 ⟨54, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (8222173570427 / 10000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (457990230333 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_55 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (16437593906351 / 20000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (143122194663 / 6250000000000 : ℝ))
      (E := (cell12403 ⟨55, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (16437593906351 / 20000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (143122194663 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_56 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (82154226692969 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144979573283 / 50000000000000 : ℝ))
      (E := (cell12403 ⟨56, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (82154226692969 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144979573283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_57 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (82120507160031 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144981563037 / 50000000000000 : ℝ))
      (E := (cell12403 ⟨57, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (82120507160031 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144981563037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_58 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (82086810905197 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144983583919 / 50000000000000 : ℝ))
      (E := (cell12403 ⟨58, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (82086810905197 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144983583919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_59 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (4102656895043 / 5000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144985574943 / 50000000000000 : ℝ))
      (E := (cell12403 ⟨59, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (4102656895043 / 5000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144985574943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12404_40 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (82696925173507 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289758960917 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨40, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (82696925173507 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289758960917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_41 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (82662829634929 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144881501671 / 50000000000000 : ℝ))
      (E := (cell12404 ⟨41, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (82662829634929 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144881501671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_42 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (41314378917553 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289766963107 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨42, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (41314378917553 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289766963107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_43 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (20648677436029 / 25000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289770957349 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨43, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (20648677436029 / 25000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289770957349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_44 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (82560685332191 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (572443746387 / 25000000000000 : ℝ))
      (E := (cell12404 ⟨44, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (82560685332191 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (572443746387 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_45 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (5157917785607 / 6250000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (228977898813 / 10000000000000 : ℝ))
      (E := (cell12404 ⟨45, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (5157917785607 / 6250000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (228977898813 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_46 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (10311588428401 / 12500000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (228978296407 / 10000000000000 : ℝ))
      (E := (cell12404 ⟨46, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (10311588428401 / 12500000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (228978296407 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_47 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (82458753875359 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144893485503 / 50000000000000 : ℝ))
      (E := (cell12404 ⟨47, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (82458753875359 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144893485503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_48 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (8242482388499 / 10000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (457958189729 / 20000000000000 : ℝ))
      (E := (cell12404 ⟨48, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (8242482388499 / 10000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (457958189729 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_49 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (3295636697083 / 4000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (447225577 / 19531250000 : ℝ))
      (E := (cell12404 ⟨49, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (3295636697083 / 4000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (447225577 / 19531250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_50 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (82357034472733 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289798985973 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨50, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (82357034472733 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289798985973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_51 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (8232317499323 / 10000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289802982833 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨51, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (8232317499323 / 10000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289802982833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_52 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (20572334739993 / 25000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (457961388501 / 20000000000000 : ℝ))
      (E := (cell12404 ⟨52, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (20572334739993 / 25000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (457961388501 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_53 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (1285242599133 / 1562500000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289810980509 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨53, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (1285242599133 / 1562500000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289810980509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_54 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (16444347423709 / 20000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (45796299523 / 2000000000000 : ℝ))
      (E := (cell12404 ⟨54, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (16444347423709 / 20000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (45796299523 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_55 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (20546992813477 / 25000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289818985547 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨55, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (20546992813477 / 25000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289818985547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_56 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (82154228722577 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144911473259 / 50000000000000 : ℝ))
      (E := (cell12404 ⟨56, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (82154228722577 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144911473259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_57 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (8212050949667 / 10000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (286228371741 / 12500000000000 : ℝ))
      (E := (cell12404 ⟨57, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (8212050949667 / 10000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (286228371741 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_58 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (16417362709689 / 20000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289830946057 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨58, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (16417362709689 / 20000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289830946057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_59 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (16410628170059 / 20000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289834977451 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨59, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (16410628170059 / 20000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289834977451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12405_40 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (16539384446711 / 20000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289622856287 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨40, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (16539384446711 / 20000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289622856287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_41 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (10332853376103 / 12500000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (71550839881 / 3125000000000 : ℝ))
      (E := (cell12405 ⟨41, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (10332853376103 / 12500000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (71550839881 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_42 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (41314377761207 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (143101929557 / 6250000000000 : ℝ))
      (E := (cell12405 ⟨42, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (41314377761207 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (143101929557 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_43 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (16518941548881 / 20000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (572408711519 / 25000000000000 : ℝ))
      (E := (cell12405 ⟨43, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (16518941548881 / 20000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (572408711519 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_44 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (20640170911257 / 25000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (457927770781 / 20000000000000 : ℝ))
      (E := (cell12405 ⟨44, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (20640170911257 / 25000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (457927770781 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_45 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (10315835399333 / 12500000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289642836827 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨45, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (10315835399333 / 12500000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289642836827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_46 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (16498541272769 / 20000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (35775732073 / 1562500000000 : ℝ))
      (E := (cell12405 ⟨46, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (16498541272769 / 20000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (35775732073 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_47 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (329835012493 / 400000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (286206355173 / 12500000000000 : ℝ))
      (E := (cell12405 ⟨47, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (329835012493 / 400000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (286206355173 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_48 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (41212411721853 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (228965486041 / 10000000000000 : ℝ))
      (E := (cell12405 ⟨48, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (41212411721853 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (228965486041 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_49 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (82390917296187 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (457931769843 / 20000000000000 : ℝ))
      (E := (cell12405 ⟨49, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (82390917296187 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (457931769843 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_50 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (41178517325907 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1144831432431 / 50000000000000 : ℝ))
      (E := (cell12405 ⟨50, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (41178517325907 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1144831432431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_51 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (82323175481851 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289666846339 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨51, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (82323175481851 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289666846339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_52 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (20572334939427 / 25000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (572417712583 / 25000000000000 : ℝ))
      (E := (cell12405 ⟨52, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (20572334939427 / 25000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (572417712583 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_53 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (82255527450937 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (114483743719 / 5000000000000 : ℝ))
      (E := (cell12405 ⟨53, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (82255527450937 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (114483743719 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_54 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (41110869266617 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289678856767 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨54, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (41110869266617 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289678856767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_55 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (82187972976437 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (572420713403 / 25000000000000 : ℝ))
      (E := (cell12405 ⟨55, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (82187972976437 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (572420713403 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_56 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (41077115376261 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1118011163 / 48828125000 : ℝ))
      (E := (cell12405 ⟨56, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (41077115376261 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1118011163 / 48828125000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_57 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (10265063979201 / 12500000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (457938175621 / 20000000000000 : ℝ))
      (E := (cell12405 ⟨57, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (10265063979201 / 12500000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (457938175621 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_58 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (41043408095977 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1144847419901 / 50000000000000 : ℝ))
      (E := (cell12405 ⟨58, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (41043408095977 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1144847419901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_59 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (41026571899977 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289698861463 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨59, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (41026571899977 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289698861463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12406_40 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (20674229823639 / 25000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (228948680691 / 10000000000000 : ℝ))
      (E := (cell12406 ⟨40, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (20674229823639 / 25000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (228948680691 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_41 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (41331412191817 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144745402179 / 50000000000000 : ℝ))
      (E := (cell12406 ⟨41, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (41331412191817 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144745402179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_42 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (41314376605299 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289494838097 / 100000000000000 : ℝ))
      (E := (cell12406 ⟨42, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (41314376605299 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289494838097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_43 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (8259470574553 / 10000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144749395123 / 50000000000000 : ℝ))
      (E := (cell12406 ⟨43, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (8259470574553 / 10000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144749395123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_44 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (41280340979331 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144751418291 / 50000000000000 : ℝ))
      (E := (cell12406 ⟨44, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (41280340979331 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144751418291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_45 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (660213454563 / 800000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289506799929 / 100000000000000 : ℝ))
      (E := (cell12406 ⟨45, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (660213454563 / 800000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289506799929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_46 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (41246352650601 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289510796907 / 100000000000000 : ℝ))
      (E := (cell12406 ⟨46, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (41246352650601 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289510796907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_47 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (82458752371823 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (114475741317 / 5000000000000 : ℝ))
      (E := (cell12406 ⟨47, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (82458752371823 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (114475741317 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_48 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (16484964600613 / 20000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (457903765587 / 20000000000000 : ℝ))
      (E := (cell12406 ⟨48, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (16484964600613 / 20000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (457903765587 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_49 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (5149432322869 / 6250000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (572380700003 / 25000000000000 : ℝ))
      (E := (cell12406 ⟨49, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (5149432322869 / 6250000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (572380700003 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_50 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (82357034831461 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (457905359927 / 20000000000000 : ℝ))
      (E := (cell12406 ⟨50, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (82357034831461 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (457905359927 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_51 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (82323175971001 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289530824769 / 100000000000000 : ℝ))
      (E := (cell12406 ⟨51, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (82323175971001 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289530824769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_52 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (41144670277967 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (286191851771 / 12500000000000 : ℝ))
      (E := (cell12406 ⟨52, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (41144670277967 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (286191851771 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_53 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (41127764278907 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (572384706081 / 25000000000000 : ℝ))
      (E := (cell12406 ⟨53, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (41127764278907 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (572384706081 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_54 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (82221739948337 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (28619284919 / 1250000000000 : ℝ))
      (E := (cell12406 ⟨54, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (82221739948337 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (28619284919 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_55 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (4109398734967 / 5000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (572386694469 / 25000000000000 : ℝ))
      (E := (cell12406 ⟨55, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (4109398734967 / 5000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (572386694469 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_56 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (82154232782803 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144775387149 / 50000000000000 : ℝ))
      (E := (cell12406 ⟨56, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (82154232782803 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144775387149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_57 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (16424102834169 / 20000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289554779487 / 100000000000000 : ℝ))
      (E := (cell12406 ⟨57, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (16424102834169 / 20000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289554779487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_58 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (82086818835723 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (457911757987 / 20000000000000 : ℝ))
      (E := (cell12406 ⟨58, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (82086818835723 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (457911757987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_59 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (20513286687459 / 25000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289562801923 / 100000000000000 : ℝ))
      (E := (cell12406 ⟨59, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (20513286687459 / 25000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289562801923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12407_40 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (8269691635651 / 10000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289350812787 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨40, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (8269691635651 / 10000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289350812787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_41 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (82662821759357 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (286169355823 / 12500000000000 : ℝ))
      (E := (cell12407 ⟨41, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (82662821759357 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (286169355823 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_42 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (82628750899657 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289358799897 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨42, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (82628750899657 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289358799897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_43 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (20648675936873 / 25000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (114468139493 / 5000000000000 : ℝ))
      (E := (cell12407 ⟨43, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (20648675936873 / 25000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (114468139493 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_44 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (82560680273093 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (457873363191 / 20000000000000 : ℝ))
      (E := (cell12407 ⟨44, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (82560680273093 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (457873363191 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_45 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (16505336089369 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144685409301 / 50000000000000 : ℝ))
      (E := (cell12407 ⟨45, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (16505336089369 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144685409301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_46 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (82492704239279 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (91574991871 / 4000000000000 : ℝ))
      (E := (cell12407 ⟨46, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (82492704239279 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (91574991871 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_47 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (82458751621077 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289378808111 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨47, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (82458751621077 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289378808111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_48 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (20606205640767 / 25000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (286172849039 / 12500000000000 : ℝ))
      (E := (cell12407 ⟨48, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (20606205640767 / 25000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (286172849039 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_49 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (41195458518113 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289386806631 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨49, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (41195458518113 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289386806631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_50 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (41178517505837 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144695395147 / 50000000000000 : ℝ))
      (E := (cell12407 ⟨50, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (41178517505837 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144695395147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_51 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (41161588230339 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (572348700043 / 25000000000000 : ℝ))
      (E := (cell12407 ⟨51, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (41161588230339 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (572348700043 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_52 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (82289341354649 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (71543713563 / 3125000000000 : ℝ))
      (E := (cell12407 ⟨52, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (82289341354649 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (71543713563 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_53 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (82255529665141 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (286175353793 / 12500000000000 : ℝ))
      (E := (cell12407 ⟨53, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (82255529665141 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (286175353793 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_54 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (20555435340963 / 25000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289406786411 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨54, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (20555435340963 / 25000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289406786411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_55 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (41093988211309 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289410817411 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨55, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (41093988211309 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289410817411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_56 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (82154234813421 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289414802129 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨56, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (82154234813421 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289414802129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_57 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (4106025825419 / 5000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144709398157 / 50000000000000 : ℝ))
      (E := (cell12407 ⟨57, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (4106025825419 / 5000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144709398157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_58 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (41043410739877 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144711398227 / 50000000000000 : ℝ))
      (E := (cell12407 ⟨58, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (41043410739877 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144711398227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_59 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (4102657484997 / 5000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144713399417 / 50000000000000 : ℝ))
      (E := (cell12407 ⟨59, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (4102657484997 / 5000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144713399417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12408_40 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (10337114177427 / 12500000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289214873919 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨40, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (10337114177427 / 12500000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289214873919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_41 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (16532563827199 / 20000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (457843777077 / 20000000000000 : ℝ))
      (E := (cell12408 ⟨41, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (16532563827199 / 20000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (457843777077 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_42 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (10328593573699 / 12500000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289222875843 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨42, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (10328593573699 / 12500000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289222875843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_43 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (8259470175029 / 10000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (572306725927 / 25000000000000 : ℝ))
      (E := (cell12408 ⟨43, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (8259470175029 / 10000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (572306725927 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_44 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (41280339294161 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (457846170167 / 20000000000000 : ℝ))
      (E := (cell12408 ⟨44, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (41280339294161 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (457846170167 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_45 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (82526679074073 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289234892847 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨45, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (82526679074073 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289234892847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_46 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (20623175794519 / 25000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289238852279 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨46, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (20623175794519 / 25000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289238852279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_47 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (82458750871013 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144621452231 / 50000000000000 : ℝ))
      (E := (cell12408 ⟨47, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (82458750871013 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144621452231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_48 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (82424822123713 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289246871357 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨48, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (82424822123713 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289246871357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_49 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (5149432306697 / 6250000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (91570034763 / 4000000000000 : ℝ))
      (E := (cell12408 ⟨49, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (5149432306697 / 6250000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (91570034763 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_50 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (82357035192453 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289254895793 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨50, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (82357035192453 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289254895793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_51 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (82323176950883 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (4578517781 / 200000000000 : ℝ))
      (E := (cell12408 ⟨51, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (82323176950883 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (4578517781 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_52 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (41144671076927 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (572315712719 / 25000000000000 : ℝ))
      (E := (cell12408 ⟨52, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (41144671076927 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (572315712719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_53 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (2056388269323 / 2500000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144633446219 / 50000000000000 : ℝ))
      (E := (cell12408 ⟨53, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (2056388269323 / 2500000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144633446219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_54 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (4111087138989 / 5000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (286158861811 / 12500000000000 : ℝ))
      (E := (cell12408 ⟨54, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (4111087138989 / 5000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (286158861811 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_55 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (82187978146271 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (91570994163 / 4000000000000 : ℝ))
      (E := (cell12408 ⟨55, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (82187978146271 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (91570994163 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_56 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (10269279605547 / 12500000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289278886223 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨56, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (10269279605547 / 12500000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289278886223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_57 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (41060259423107 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (457856573893 / 20000000000000 : ℝ))
      (E := (cell12408 ⟨57, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (41060259423107 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (457856573893 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_58 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (16417364824809 / 20000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144643429681 / 50000000000000 : ℝ))
      (E := (cell12408 ⟨58, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (16417364824809 / 20000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144643429681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_59 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (82053152650267 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (572322713049 / 25000000000000 : ℝ))
      (E := (cell12408 ⟨59, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (82053152650267 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (572322713049 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12409_40 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (3307876419331 / 4000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (572269747577 / 25000000000000 : ℝ))
      (E := (cell12409 ⟨40, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (3307876419331 / 4000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (572269747577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_41 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (16532563302709 / 20000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (572270744877 / 25000000000000 : ℝ))
      (E := (cell12409 ⟨41, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (16532563302709 / 20000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (572270744877 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_42 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (206571865701 / 250000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144543503587 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨42, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (206571865701 / 250000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144543503587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_43 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (82594699753923 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (457818202843 / 20000000000000 : ℝ))
      (E := (cell12409 ⟨43, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (82594699753923 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (457818202843 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_44 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (20640169226087 / 25000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144547500019 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨44, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (20640169226087 / 25000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144547500019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_45 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (4126333885103 / 5000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (457819804533 / 20000000000000 : ℝ))
      (E := (cell12409 ⟨45, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (4126333885103 / 5000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (457819804533 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_46 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (82492702117593 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144551511139 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨46, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (82492702117593 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144551511139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_47 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (8245875012163 / 10000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (228910699763 / 10000000000000 : ℝ))
      (E := (cell12409 ⟨47, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (8245875012163 / 10000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (228910699763 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_48 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (16484964337 / 20000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144555503083 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨48, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (16484964337 / 20000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144555503083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_49 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (41195458389341 / 50000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (457822997469 / 20000000000000 : ℝ))
      (E := (cell12409 ⟨49, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (41195458389341 / 50000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (457822997469 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_50 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (41178517686899 / 50000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (572279749557 / 25000000000000 : ℝ))
      (E := (cell12409 ⟨50, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (41178517686899 / 50000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (572279749557 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_51 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (16464635488323 / 20000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (572280744451 / 25000000000000 : ℝ))
      (E := (cell12409 ⟨51, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (16464635488323 / 20000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (572280744451 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_52 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (82289342953547 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (71535218211 / 3125000000000 : ℝ))
      (E := (cell12409 ⟨52, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (82289342953547 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (71535218211 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_53 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (82255531881149 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (228913101061 / 10000000000000 : ℝ))
      (E := (cell12409 ⟨53, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (82255531881149 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (228913101061 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_54 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (2055543604903 / 2500000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144567499829 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨54, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (2055543604903 / 2500000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144567499829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_55 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (82187979870299 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144569503007 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨55, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (82187979870299 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144569503007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_56 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (82154238875667 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289143026583 / 100000000000000 : ℝ))
      (E := (cell12409 ⟨56, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (82154238875667 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289143026583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_57 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (41060260592173 / 50000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144573499473 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨57, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (41060260592173 / 50000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144573499473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_58 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (20521706692149 / 25000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289150978661 / 100000000000000 : ℝ))
      (E := (cell12409 ⟨58, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (20521706692149 / 25000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289150978661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_59 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (5128322225051 / 6250000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289155021177 / 100000000000000 : ℝ))
      (E := (cell12409 ⟨59, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (5128322225051 / 6250000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289155021177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12410_40 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (41348453774043 / 50000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288943220671 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨40, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (41348453774043 / 50000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288943220671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_41 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (82662813892009 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288947187691 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨41, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (82662813892009 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288947187691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_42 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (82628743972083 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (71529724809 / 3125000000000 : ℝ))
      (E := (cell12410 ⟨42, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (82628743972083 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (71529724809 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_43 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (10324337219799 / 12500000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (286119397521 / 12500000000000 : ℝ))
      (E := (cell12410 ⟨43, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (10324337219799 / 12500000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (286119397521 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_44 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (82560675221171 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (9155836819 / 400000000000 : ℝ))
      (E := (cell12410 ⟨44, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (82560675221171 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (9155836819 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_45 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (16505335266161 / 20000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (286120401007 / 12500000000000 : ℝ))
      (E := (cell12410 ⟨45, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (16505335266161 / 20000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (286120401007 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_46 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (82492701057829 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (457793437811 / 20000000000000 : ℝ))
      (E := (cell12410 ⟨46, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (82492701057829 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (457793437811 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_47 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (161052244869 / 195312500000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288971205381 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨47, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (161052244869 / 195312500000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288971205381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_48 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (82424821246931 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (457795039347 / 20000000000000 : ℝ))
      (E := (cell12410 ⟨48, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (82424821246931 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (457795039347 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_49 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (1287358072669 / 1562500000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288979161439 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨49, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (1287358072669 / 1562500000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288979161439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_50 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (20589258888927 / 25000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288983156551 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨50, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (20589258888927 / 25000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288983156551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_51 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (658585423463 / 800000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (457797436007 / 20000000000000 : ℝ))
      (E := (cell12410 ⟨51, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (658585423463 / 800000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (457797436007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_52 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (8228934375373 / 10000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (28612389633 / 1250000000000 : ℝ))
      (E := (cell12410 ⟨52, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (8228934375373 / 10000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (28612389633 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_53 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (82255532989829 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288995184859 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨53, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (82255532989829 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288995184859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_54 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (82221745612873 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (1144499580483 / 50000000000000 : ℝ))
      (E := (cell12410 ⟨54, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (82221745612873 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (1144499580483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_55 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (82187981594701 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (1144501607077 / 50000000000000 : ℝ))
      (E := (cell12410 ⟨55, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (82187981594701 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (1144501607077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_56 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (16430848181459 / 20000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (143062947757 / 6250000000000 : ℝ))
      (E := (cell12410 ⟨56, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (16430848181459 / 20000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (143062947757 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_57 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (82120523522777 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (143063199047 / 6250000000000 : ℝ))
      (E := (cell12410 ⟨57, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (82120523522777 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (143063199047 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_58 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (2565213419169 / 3125000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2289015213491 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨58, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (2565213419169 / 3125000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2289015213491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_59 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (20513289637897 / 25000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2289019187443 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨59, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (20513289637897 / 25000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2289019187443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12411_40 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (82696904613849 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (91552297903 / 4000000000000 : ℝ))
      (E := (cell12411 ⟨40, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (82696904613849 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (91552297903 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_41 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (41331405635693 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144405725599 / 50000000000000 : ℝ))
      (E := (cell12411 ⟨41, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (41331405635693 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144405725599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_42 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (82628741664641 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288815435987 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨42, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (82628741664641 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288815435987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_43 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (5162168485231 / 6250000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (57220486509 / 2500000000000 : ℝ))
      (E := (cell12411 ⟨43, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (5162168485231 / 6250000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (57220486509 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_44 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (8256067353879 / 10000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288823406163 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨44, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (8256067353879 / 10000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288823406163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_45 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (20631668740077 / 25000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288827449023 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨45, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (20631668740077 / 25000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288827449023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_46 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (16498539999757 / 20000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288831411469 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨46, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (16498539999757 / 20000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288831411469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_47 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (41229374312453 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (45776708199 / 2000000000000 : ℝ))
      (E := (cell12411 ⟨47, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (41229374312453 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (45776708199 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_48 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (82424820809503 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288839443071 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨48, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (82424820809503 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288839443071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_49 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (41195458261777 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (572210862573 / 25000000000000 : ℝ))
      (E := (cell12411 ⟨49, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (41195458261777 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (572210862573 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_50 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (82357035738183 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (57221185743 / 2500000000000 : ℝ))
      (E := (cell12411 ⟨50, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (82357035738183 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (57221185743 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_51 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (82323178424661 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288851438221 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨51, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (82323178424661 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288851438221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_52 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (82289344554401 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144427707273 / 50000000000000 : ℝ))
      (E := (cell12411 ⟨52, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (82289344554401 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144427707273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_53 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (1028194176237 / 1250000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144429707593 / 50000000000000 : ℝ))
      (E := (cell12411 ⟨53, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (1028194176237 / 1250000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144429707593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_54 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (41110873515019 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (457772687493 / 20000000000000 : ℝ))
      (E := (cell12411 ⟨54, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (41110873515019 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (457772687493 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_55 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (20546995829869 / 25000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288867419429 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨55, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (20546995829869 / 25000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288867419429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_56 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (41077121469629 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (572217854251 / 25000000000000 : ℝ))
      (E := (cell12411 ⟨56, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (41077121469629 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (572217854251 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_57 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (16424105172301 / 20000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288875426889 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨57, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (16424105172301 / 20000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288875426889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_58 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (1026085400731 / 1250000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288879445571 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨58, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (1026085400731 / 1250000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288879445571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_59 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (41026580751291 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (572220852541 / 25000000000000 : ℝ))
      (E := (cell12411 ⟨59, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (41026580751291 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (572220852541 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12412_40 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (20674225420141 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144335864869 / 50000000000000 : ℝ))
      (E := (cell12412 ⟨40, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (20674225420141 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144335864869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_41 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (20665702162919 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (572168927821 / 25000000000000 : ℝ))
      (E := (cell12412 ⟨41, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (20665702162919 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (572168927821 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_42 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (82628739358071 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144339866737 / 50000000000000 : ℝ))
      (E := (cell12412 ⟨42, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (82628739358071 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144339866737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_43 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (20648673442459 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288683737211 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨43, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (20648673442459 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288683737211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_44 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (41280335928603 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288687721901 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨44, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (41280335928603 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288687721901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_45 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (10315834198821 / 12500000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144345872783 / 50000000000000 : ℝ))
      (E := (cell12412 ⟨45, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (10315834198821 / 12500000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144345872783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_46 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (4124634947023 / 5000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288695748383 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨46, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (4124634947023 / 5000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288695748383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_47 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (16491749575513 / 20000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (457739945821 / 20000000000000 : ℝ))
      (E := (cell12412 ⟨47, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (16491749575513 / 20000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (457739945821 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_48 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (82424820372717 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (572175936293 / 25000000000000 : ℝ))
      (E := (cell12412 ⟨48, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (82424820372717 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (572175936293 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_49 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (16478183279379 / 20000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288707736043 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨49, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (16478183279379 / 20000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288707736043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_50 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (10294629490153 / 12500000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144355879389 / 50000000000000 : ℝ))
      (E := (cell12412 ⟨50, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (10294629490153 / 12500000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144355879389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_51 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (41161589458487 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288715752361 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨51, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (41161589458487 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288715752361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_52 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (2057233633889 / 2500000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288719714469 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨52, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (2057233633889 / 2500000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288719714469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_53 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (4112776760427 / 5000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144361880309 / 50000000000000 : ℝ))
      (E := (cell12412 ⟨53, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (4112776760427 / 5000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144361880309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_54 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (16444349689523 / 20000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144363855529 / 50000000000000 : ℝ))
      (E := (cell12412 ⟨54, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (16444349689523 / 20000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144363855529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_55 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (41093992522313 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288731739979 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨55, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (41093992522313 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288731739979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_56 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (82154244971557 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288735726163 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨56, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (82154244971557 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288735726163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_57 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (20530132050133 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (457747945071 / 20000000000000 : ℝ))
      (E := (cell12412 ⟨57, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (20530132050133 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (457747945071 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_58 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (82086834703811 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (572185933511 / 25000000000000 : ℝ))
      (E := (cell12412 ⟨58, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (82086834703811 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (572185933511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_59 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (41026582226899 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144373874253 / 50000000000000 : ℝ))
      (E := (cell12412 ⟨59, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (41026582226899 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144373874253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12413_40 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (8269689874823 / 10000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (57213403147 / 2500000000000 : ℝ))
      (E := (cell12413 ⟨40, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (8269689874823 / 10000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (57213403147 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_41 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (41331403016439 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288540085437 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨41, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (41331403016439 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288540085437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_42 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (10328592131547 / 12500000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144272043173 / 50000000000000 : ℝ))
      (E := (cell12413 ⟨42, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (10328592131547 / 12500000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144272043173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_43 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (8259469177681 / 10000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288548069513 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨43, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (8259469177681 / 10000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288548069513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_44 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (82560670176417 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288552093153 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨44, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (82560670176417 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288552093153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_45 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (41263336110793 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (457711219537 / 20000000000000 : ℝ))
      (E := (cell12413 ⟨45, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (41263336110793 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (457711219537 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_46 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (82492697882853 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288560082077 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨46, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (82492697882853 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288560082077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_47 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (10307343391363 / 12500000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288564103963 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨47, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (10307343391363 / 12500000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288564103963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_48 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (82424819936573 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144284051519 / 50000000000000 : ℝ))
      (E := (cell12413 ⟨48, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (82424819936573 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144284051519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_49 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (82390916270839 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (286071509703 / 12500000000000 : ℝ))
      (E := (cell12413 ⟨49, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (82390916270839 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (286071509703 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_50 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (82357036104829 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (286072010597 / 12500000000000 : ℝ))
      (E := (cell12413 ⟨50, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (82357036104829 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (286072010597 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_51 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (82323179409813 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288580122457 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨51, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (82323179409813 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288580122457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_52 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (10286168269651 / 12500000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (228858407041 / 10000000000000 : ℝ))
      (E := (cell12413 ⟨52, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (10286168269651 / 12500000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (228858407041 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_53 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (82255536318571 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144294051553 / 50000000000000 : ℝ))
      (E := (cell12413 ⟨53, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (82255536318571 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144294051553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_54 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (20555437466401 / 25000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144296049921 / 50000000000000 : ℝ))
      (E := (cell12413 ⟨54, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (20555437466401 / 25000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144296049921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_55 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (1643759735403 / 2000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144298058367 / 50000000000000 : ℝ))
      (E := (cell12413 ⟨55, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (1643759735403 / 2000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144298058367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_56 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (2567320218881 / 3125000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288600091591 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨56, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (2567320218881 / 3125000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288600091591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_57 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (5132533158741 / 6250000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288604080153 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨57, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (5132533158741 / 6250000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288604080153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_58 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (82086837349403 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (228860807891 / 10000000000000 : ℝ))
      (E := (cell12413 ⟨58, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (82086837349403 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (228860807891 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_59 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (20513291851309 / 25000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144306042069 / 50000000000000 : ℝ))
      (E := (cell12413 ⟨59, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (20513291851309 / 25000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144306042069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12414_40 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (41348447908423 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288400518567 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨40, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (41348447908423 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288400518567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_41 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (5166425213437 / 6250000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (572101128729 / 25000000000000 : ℝ))
      (E := (cell12414 ⟨41, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (5166425213437 / 6250000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (572101128729 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_42 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (41314367373777 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (143025530913 / 6250000000000 : ℝ))
      (E := (cell12414 ⟨42, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (41314367373777 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (143025530913 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_43 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (41297344892309 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288412516057 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨43, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (41297344892309 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288412516057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_44 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (10320083562053 / 12500000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288416519921 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨44, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (10320083562053 / 12500000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288416519921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_45 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (1031583385667 / 1250000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (457684101077 / 20000000000000 : ℝ))
      (E := (cell12414 ⟨45, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (1031583385667 / 1250000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (457684101077 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_46 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (16498539365193 / 20000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144212265137 / 50000000000000 : ℝ))
      (E := (cell12414 ⟨46, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (16498539365193 / 20000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144212265137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_47 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (82458746384923 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144214267263 / 50000000000000 : ℝ))
      (E := (cell12414 ⟨47, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (82458746384923 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144214267263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_48 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (8242481950107 / 10000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144216258337 / 50000000000000 : ℝ))
      (E := (cell12414 ⟨48, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (8242481950107 / 10000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144216258337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_49 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (41195458072693 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144218266983 / 50000000000000 : ℝ))
      (E := (cell12414 ⟨49, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (41195458072693 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144218266983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_50 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (82357036288999 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288440525621 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨50, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (82357036288999 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288440525621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_51 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (82323179903179 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (228844448953 / 10000000000000 : ℝ))
      (E := (cell12414 ⟨51, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (82323179903179 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (228844448953 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_52 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (5143084184959 / 6250000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288448541371 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨52, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (5143084184959 / 6250000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288448541371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_53 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (82255537429051 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (572113125419 / 25000000000000 : ℝ))
      (E := (cell12414 ⟨53, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (82255537429051 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (572113125419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_54 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (16444350256801 / 20000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288456485723 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨54, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (16444350256801 / 20000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288456485723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_55 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (82187988496047 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144230245313 / 50000000000000 : ℝ))
      (E := (cell12414 ⟨55, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (82187988496047 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144230245313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_56 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (82154249037163 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (286058064161 / 12500000000000 : ℝ))
      (E := (cell12414 ⟨56, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (82154249037163 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (286058064161 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_57 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (82120532879477 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (572117122821 / 25000000000000 : ℝ))
      (E := (cell12414 ⟨57, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (82120532879477 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (572117122821 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_58 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (41043419997627 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144236269657 / 50000000000000 : ℝ))
      (E := (cell12414 ⟨58, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (41043419997627 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144236269657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_59 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (2564161573653 / 3125000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288476535393 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨59, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (2564161573653 / 3125000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288476535393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12415_40 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (41348446443207 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (572066256309 / 25000000000000 : ℝ))
      (E := (cell12415 ⟨40, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (41348446443207 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (572066256309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_41 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (41331400399009 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144134499861 / 50000000000000 : ℝ))
      (E := (cell12415 ⟨41, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (41331400399009 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144134499861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_42 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (20657183110901 / 25000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (572068254257 / 25000000000000 : ℝ))
      (E := (cell12415 ⟨42, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (20657183110901 / 25000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (572068254257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_43 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (82594687793261 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (457655403611 / 20000000000000 : ℝ))
      (E := (cell12415 ⟨43, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (82594687793261 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (457655403611 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_44 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (82560666817227 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144140501103 / 50000000000000 : ℝ))
      (E := (cell12415 ⟨44, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (82560666817227 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144140501103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_45 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (20631667371473 / 25000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288284968663 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨45, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (20631667371473 / 25000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288284968663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_46 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (16498539153959 / 20000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288288975253 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨46, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (16498539153959 / 20000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288288975253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_47 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (41229372819811 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (572073255199 / 25000000000000 : ℝ))
      (E := (cell12415 ⟨47, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (41229372819811 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (572073255199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_48 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (2575775595819 / 3125000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288296986079 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨48, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (2575775595819 / 3125000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288296986079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_49 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (10298864502567 / 12500000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (228830098721 / 10000000000000 : ℝ))
      (E := (cell12415 ⟨49, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (10298864502567 / 12500000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (228830098721 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_50 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (82357036473733 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144152511181 / 50000000000000 : ℝ))
      (E := (cell12415 ⟨50, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (82357036473733 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144152511181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_51 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (82323180397071 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (114415448577 / 5000000000000 : ℝ))
      (E := (cell12415 ⟨51, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (82323180397071 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (114415448577 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_52 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (82289347761967 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288313009353 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨52, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (82289347761967 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288313009353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_53 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (41127769269991 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144158507677 / 50000000000000 : ℝ))
      (E := (cell12415 ⟨53, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (41127769269991 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144158507677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_54 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (82221752702817 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288320986799 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨54, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (82221752702817 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288320986799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_55 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (41093995111159 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288324979799 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨55, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (41093995111159 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288324979799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_56 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (82154251070469 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288328991257 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨56, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (82154251070469 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288328991257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_57 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (20530133804849 / 25000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (572083254467 / 25000000000000 : ℝ))
      (E := (cell12415 ⟨57, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (20530133804849 / 25000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (572083254467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_58 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (16417368528273 / 20000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288336996971 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨58, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (16417368528273 / 20000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288336996971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_59 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (82053173308777 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144170491971 / 50000000000000 : ℝ))
      (E := (cell12415 ⟨59, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (82053173308777 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144170491971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12416_40 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (20674222489233 / 25000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288129528449 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨40, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (20674222489233 / 25000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288129528449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_41 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (16532559636391 / 20000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (143008346241 / 6250000000000 : ℝ))
      (E := (cell12416 ⟨41, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (16532559636391 / 20000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (143008346241 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_42 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (5164295633783 / 6250000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288137536071 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨42, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (5164295633783 / 6250000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288137536071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_43 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (41297342901369 / 50000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288141516717 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨43, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (41297342901369 / 50000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288141516717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_44 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (3302426605553 / 4000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (286018192501 / 12500000000000 : ℝ))
      (E := (cell12416 ⟨44, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (3302426605553 / 4000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (286018192501 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_45 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (4126333405959 / 5000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288149546359 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨45, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (4126333405959 / 5000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288149546359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_46 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (82492694714343 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (143009595921 / 6250000000000 : ℝ))
      (E := (cell12416 ⟨46, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (82492694714343 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (143009595921 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_47 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (16491748979 / 20000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (143009843993 / 6250000000000 : ℝ))
      (E := (cell12416 ⟨47, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (16491748979 / 20000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (143009843993 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_48 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (20606204657997 / 25000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (572040377813 / 25000000000000 : ℝ))
      (E := (cell12416 ⟨48, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (20606204657997 / 25000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (572040377813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_49 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (82390915896289 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (143010347201 / 6250000000000 : ℝ))
      (E := (cell12416 ⟨49, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (82390915896289 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (143010347201 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_50 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (10294629582379 / 12500000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288169516043 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨50, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (10294629582379 / 12500000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288169516043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_51 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (82323180891489 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (572043377377 / 25000000000000 : ℝ))
      (E := (cell12416 ⟨51, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (82323180891489 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (572043377377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_52 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (82289348565079 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144088766677 / 50000000000000 : ℝ))
      (E := (cell12416 ⟨52, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (82289348565079 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144088766677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_53 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (82255539651361 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (572045381523 / 25000000000000 : ℝ))
      (E := (cell12416 ⟨53, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (82255539651361 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (572045381523 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_54 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (82221754122041 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (114409277201 / 5000000000000 : ℝ))
      (E := (cell12416 ⟨54, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (82221754122041 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (114409277201 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_55 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (82187991948961 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288189525181 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨55, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (82187991948961 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288189525181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_56 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (8215425310411 / 10000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144096762749 / 50000000000000 : ℝ))
      (E := (cell12416 ⟨56, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (8215425310411 / 10000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144096762749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_57 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (82120537559613 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (457639508333 / 20000000000000 : ℝ))
      (E := (cell12416 ⟨57, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (82120537559613 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (457639508333 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_58 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (16417369057547 / 20000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (143012594439 / 6250000000000 : ℝ))
      (E := (cell12416 ⟨58, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (16417369057547 / 20000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (143012594439 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_59 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (1025664703261 / 1250000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144102774057 / 50000000000000 : ℝ))
      (E := (cell12416 ⟨59, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (1025664703261 / 1250000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144102774057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12417_40 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (206742217571 / 250000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287994145649 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨40, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (206742217571 / 250000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287994145649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_41 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (20665698891701 / 25000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287998135319 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨41, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (20665698891701 / 25000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287998135319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_42 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (20657181959581 / 25000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (572000527627 / 25000000000000 : ℝ))
      (E := (cell12417 ⟨42, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (20657181959581 / 25000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (572000527627 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_43 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (10324335476631 / 12500000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1144003064813 / 50000000000000 : ℝ))
      (E := (cell12417 ⟨43, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (10324335476631 / 12500000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1144003064813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_44 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (41280331730609 / 50000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (228801013333 / 10000000000000 : ℝ))
      (E := (cell12417 ⟨44, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (41280331730609 / 50000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (228801013333 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_45 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (3301066670129 / 4000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1144007060401 / 50000000000000 : ℝ))
      (E := (cell12417 ⟨45, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (3301066670129 / 4000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1144007060401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_46 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (10311586707451 / 12500000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2288018149867 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨46, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (10311586707451 / 12500000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2288018149867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_47 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (82458744151057 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1144011050787 / 50000000000000 : ℝ))
      (E := (cell12417 ⟨47, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (82458744151057 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1144011050787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_48 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (10303102274801 / 12500000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1144013075553 / 50000000000000 : ℝ))
      (E := (cell12417 ⟨48, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (10303102274801 / 12500000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1144013075553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_49 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (20597728943161 / 25000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (35750470627 / 1562500000000 : ℝ))
      (E := (cell12417 ⟨49, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (20597728943161 / 25000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (35750470627 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_50 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (41178518422447 / 50000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1144017062289 / 50000000000000 : ℝ))
      (E := (cell12417 ⟨50, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (41178518422447 / 50000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1144017062289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_51 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (82323181386433 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (572009525859 / 25000000000000 : ℝ))
      (E := (cell12417 ⟨51, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (82323181386433 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (572009525859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_52 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (82289349368677 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (114402105669 / 5000000000000 : ℝ))
      (E := (cell12417 ⟨52, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (82289349368677 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (114402105669 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_53 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (8225554076319 / 10000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2288046151941 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨53, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (8225554076319 / 10000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2288046151941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_54 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (3288870221667 / 4000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (143003134837 / 6250000000000 : ℝ))
      (E := (cell12417 ⟨54, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (3288870221667 / 4000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (143003134837 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_55 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (41093996837989 / 50000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1144027063387 / 50000000000000 : ℝ))
      (E := (cell12417 ⟨55, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (41093996837989 / 50000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1144027063387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_56 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (82154255138087 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (572014529003 / 25000000000000 : ℝ))
      (E := (cell12417 ⟨56, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (82154255138087 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (572014529003 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_57 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (41060269950063 / 50000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2288062121801 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨57, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (41060269950063 / 50000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2288062121801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_58 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (20521711983591 / 25000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (114403307031 / 5000000000000 : ℝ))
      (E := (cell12417 ⟨58, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (20521711983591 / 25000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (114403307031 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_59 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (16410635842641 / 20000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1144035054791 / 50000000000000 : ℝ))
      (E := (cell12417 ⟨59, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (16410635842641 / 20000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1144035054791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12418_40 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (82696884100817 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (571964689849 / 25000000000000 : ℝ))
      (E := (cell12418 ⟨40, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (82696884100817 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (571964689849 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_41 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (20665698238141 / 25000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (35747856033 / 1562500000000 : ℝ))
      (E := (cell12418 ⟨41, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (20665698238141 / 25000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (35747856033 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_42 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (2582147673031 / 3125000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2234244921 / 97656250000 : ℝ))
      (E := (cell12418 ⟨42, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (2582147673031 / 3125000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2234244921 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_43 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (1290541903503 / 1562500000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (228787079799 / 10000000000000 : ℝ))
      (E := (cell12418 ⟨43, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (1290541903503 / 1562500000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (228787079799 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_44 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (41280330892203 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287874782171 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨44, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (41280330892203 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287874782171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_45 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (41263332694013 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287878809663 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨45, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (41263332694013 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287878809663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_46 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (10311586575699 / 12500000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (114394138089 / 5000000000000 : ℝ))
      (E := (cell12418 ⟨46, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (10311586575699 / 12500000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (114394138089 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_47 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (41229371703897 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287886754967 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨47, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (41229371703897 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287886754967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_48 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (82424817765469 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (142993174239 / 6250000000000 : ℝ))
      (E := (cell12418 ⟨48, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (82424817765469 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (142993174239 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_49 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (41195457824801 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287894799803 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨49, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (41195457824801 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287894799803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_50 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (82357037031321 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287898789009 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨50, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (82357037031321 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287898789009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_51 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (41161590940951 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (91516110133 / 4000000000000 : ℝ))
      (E := (cell12418 ⟨51, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (41161590940951 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (91516110133 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_52 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (20572337543191 / 25000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287906808429 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨52, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (20572337543191 / 25000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287906808429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_53 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (20563885468867 / 25000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (45758215497 / 2000000000000 : ℝ))
      (E := (cell12418 ⟨53, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (20563885468867 / 25000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (45758215497 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_54 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (82221756961721 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143957383931 / 50000000000000 : ℝ))
      (E := (cell12418 ⟨54, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (82221756961721 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143957383931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_55 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (10273499425421 / 12500000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143959392289 / 50000000000000 : ℝ))
      (E := (cell12418 ⟨55, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (10273499425421 / 12500000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143959392289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_56 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (41077128586199 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (5719806907 / 250000000000 : ℝ))
      (E := (cell12418 ⟨56, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (41077128586199 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (5719806907 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_57 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (82120542240937 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (228792675827 / 10000000000000 : ℝ))
      (E := (cell12418 ⟨57, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (82120542240937 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (228792675827 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_58 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (82086850581253 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (228793076747 / 10000000000000 : ℝ))
      (E := (cell12418 ⟨58, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (82086850581253 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (228793076747 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_59 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (328212728663 / 400000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287934786677 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨59, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (328212728663 / 400000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287934786677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12419_40 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (16539376234837 / 20000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287723487129 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨40, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (16539376234837 / 20000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287723487129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_41 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (41331395169617 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287727492237 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨41, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (41331395169617 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287727492237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_42 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (82628723236531 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287731484329 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨42, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (82628723236531 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287731484329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_43 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (82594679836169 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287735521813 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨43, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (82594679836169 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287735521813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_44 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (20640165027097 / 25000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143869743267 / 50000000000000 : ℝ))
      (E := (cell12419 ⟨44, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (20640165027097 / 25000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143869743267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_45 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (41263332011791 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287743495273 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨45, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (41263332011791 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287743495273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_46 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (20623172888073 / 25000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (571936872051 / 25000000000000 : ℝ))
      (E := (cell12419 ⟨46, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (20623172888073 / 25000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (571936872051 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_47 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (82458742665209 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (571937880739 / 25000000000000 : ℝ))
      (E := (cell12419 ⟨47, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (82458742665209 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (571937880739 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_48 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (8242481733317 / 10000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (457551096063 / 20000000000000 : ℝ))
      (E := (cell12419 ⟨48, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (8242481733317 / 10000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (457551096063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_49 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (82390915527161 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143879738193 / 50000000000000 : ℝ))
      (E := (cell12419 ⟨49, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (82390915527161 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143879738193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_50 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (82357037218311 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (114388175467 / 5000000000000 : ℝ))
      (E := (cell12419 ⟨50, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (82357037218311 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (114388175467 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_51 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (10290397797237 / 12500000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (457553503631 / 20000000000000 : ℝ))
      (E := (cell12419 ⟨51, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (10290397797237 / 12500000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (457553503631 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_52 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (82289350977337 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287771500503 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨52, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (82289350977337 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287771500503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_53 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (16451108597639 / 20000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (285971939109 / 12500000000000 : ℝ))
      (E := (cell12419 ⟨53, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (16451108597639 / 20000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (285971939109 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_54 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (41110879191089 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287779493531 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨54, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (41110879191089 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287779493531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_55 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (82187997131131 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (457556699719 / 20000000000000 : ℝ))
      (E := (cell12419 ⟨55, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (82187997131131 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (457556699719 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_56 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (20538564801761 / 25000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (14298672031 / 625000000000 : ℝ))
      (E := (cell12419 ⟨56, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (20538564801761 / 25000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (14298672031 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_57 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (20530136145511 / 25000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287791510199 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨57, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (20530136145511 / 25000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287791510199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_58 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (205217133071 / 250000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (457559101973 / 20000000000000 : ℝ))
      (E := (cell12419 ⟨58, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (205217133071 / 250000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (457559101973 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_59 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (82053185118517 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143899760117 / 50000000000000 : ℝ))
      (E := (cell12419 ⟨59, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (82053185118517 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143899760117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12420_40 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (82696878248501 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (571897067533 / 25000000000000 : ℝ))
      (E := (cell12420 ⟨40, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (82696878248501 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (571897067533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_41 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (16532557545363 / 20000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287592253693 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨41, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (16532557545363 / 20000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287592253693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_42 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (82628720936943 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (571899070929 / 25000000000000 : ℝ))
      (E := (cell12420 ⟨42, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (82628720936943 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (571899070929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_43 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (82594677848979 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (457520048461 / 20000000000000 : ℝ))
      (E := (cell12420 ⟨43, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (82594677848979 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (457520048461 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_44 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (16512131686633 / 20000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143802123209 / 50000000000000 : ℝ))
      (E := (cell12420 ⟨44, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (16512131686633 / 20000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143802123209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_45 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (41263331329947 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (285951036913 / 12500000000000 : ℝ))
      (E := (cell12420 ⟨45, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (41263331329947 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (285951036913 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_46 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (8249269049971 / 10000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143806135137 / 50000000000000 : ℝ))
      (E := (cell12420 ⟨46, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (8249269049971 / 10000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143806135137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_47 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (82458741923303 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (571904071943 / 25000000000000 : ℝ))
      (E := (cell12420 ⟨47, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (82458741923303 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (571904071943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_48 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (10303102112689 / 12500000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2234004187 / 97656250000 : ℝ))
      (E := (cell12420 ⟨48, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (10303102112689 / 12500000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2234004187 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_49 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (41195457702661 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (285953033467 / 12500000000000 : ℝ))
      (E := (cell12420 ⟨49, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (41195457702661 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (285953033467 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_50 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (10294629675733 / 12500000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287628285571 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨50, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (10294629675733 / 12500000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287628285571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_51 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (5145198929651 / 6250000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (71488508749 / 3125000000000 : ℝ))
      (E := (cell12420 ⟨51, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (5145198929651 / 6250000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (71488508749 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_52 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (82289351782397 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143818124301 / 50000000000000 : ℝ))
      (E := (cell12420 ⟨52, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (82289351782397 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143818124301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_53 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (82255544101371 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287640247957 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨53, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (82255544101371 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287640247957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_54 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (16444351960609 / 20000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (285955534419 / 12500000000000 : ℝ))
      (E := (cell12420 ⟨54, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (16444351960609 / 20000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (285955534419 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_55 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (41093999429633 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (91505930753 / 4000000000000 : ℝ))
      (E := (cell12420 ⟨55, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (41093999429633 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (91505930753 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_56 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (10269282655253 / 12500000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (22876522843 / 1000000000000 : ℝ))
      (E := (cell12420 ⟨56, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (10269282655253 / 12500000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (22876522843 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_57 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (10265068365431 / 12500000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (457531251869 / 20000000000000 : ℝ))
      (E := (cell12420 ⟨57, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (10265068365431 / 12500000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (457531251869 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_58 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (41043427937903 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287660249517 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨58, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (41043427937903 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287660249517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_59 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (16410637614301 / 20000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (142979015693 / 6250000000000 : ℝ))
      (E := (cell12420 ⟨59, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (16410637614301 / 20000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (142979015693 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12421_40 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (82696875323767 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143726554203 / 50000000000000 : ℝ))
      (E := (cell12421 ⟨40, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (82696875323767 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143726554203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_41 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (16532557023061 / 20000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (457491414097 / 20000000000000 : ℝ))
      (E := (cell12421 ⟨41, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (16532557023061 / 20000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (457491414097 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_42 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (41314359319113 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287461079733 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨42, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (41314359319113 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287461079733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_43 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (82594675862621 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (285933134631 / 12500000000000 : ℝ))
      (E := (cell12421 ⟨43, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (82594675862621 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (285933134631 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_44 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (16512131351747 / 20000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (3574170501 / 156250000000 : ℝ))
      (E := (cell12421 ⟨44, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (16512131351747 / 20000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (3574170501 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_45 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (41263330648481 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (457494618417 / 20000000000000 : ℝ))
      (E := (cell12421 ⟨45, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (41263330648481 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (457494618417 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_46 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (20623172361961 / 25000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (571869276999 / 25000000000000 : ℝ))
      (E := (cell12421 ⟨46, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (20623172361961 / 25000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (571869276999 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_47 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (3298349647283 / 4000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287481108301 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨47, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (3298349647283 / 4000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287481108301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_48 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (82424816470493 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287485091529 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨48, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (82424816470493 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287485091529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_49 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (20597728821021 / 25000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143744557463 / 50000000000000 : ℝ))
      (E := (cell12421 ⟨49, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (20597728821021 / 25000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143744557463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_50 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (82357037593981 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287493117703 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨50, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (82357037593981 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287493117703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_51 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (4116159168573 / 5000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287497097747 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨51, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (4116159168573 / 5000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287497097747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_52 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (10286169073493 / 12500000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287501111729 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨52, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (10286169073493 / 12500000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287501111729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_53 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (16451109042999 / 20000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287505098157 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨53, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (16451109042999 / 20000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287505098157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_54 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (82221761224323 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (91500364533 / 4000000000000 : ℝ))
      (E := (cell12421 ⟨54, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (82221761224323 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (91500364533 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_55 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (41094000293887 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (228751309527 / 10000000000000 : ℝ))
      (E := (cell12421 ⟨55, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (41094000293887 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (228751309527 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_56 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (4107713163867 / 5000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (457503419983 / 20000000000000 : ℝ))
      (E := (cell12421 ⟨56, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (4107713163867 / 5000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (457503419983 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_57 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (82120549265149 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287521123951 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨57, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (82120549265149 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287521123951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_58 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (82086858523471 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143762552357 / 50000000000000 : ℝ))
      (E := (cell12421 ⟨58, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (82086858523471 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143762552357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_59 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (82053191024713 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143764548787 / 50000000000000 : ℝ))
      (E := (cell12421 ⟨59, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (82053191024713 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143764548787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12422_40 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (82696872399981 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (71478687561 / 3125000000000 : ℝ))
      (E := (cell12422 ⟨40, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (82696872399981 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (71478687561 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_41 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (41331391252353 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (457464400271 / 20000000000000 : ℝ))
      (E := (cell12422 ⟨41, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (41331391252353 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (457464400271 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_42 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (4131435817019 / 5000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (571831497479 / 25000000000000 : ℝ))
      (E := (cell12422 ⟨42, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (4131435817019 / 5000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (571831497479 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_43 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (10324334234637 / 12500000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (571832491813 / 25000000000000 : ℝ))
      (E := (cell12422 ⟨43, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (10324334234637 / 12500000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (571832491813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_44 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (82560655085099 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (1143666995787 / 50000000000000 : ℝ))
      (E := (cell12422 ⟨44, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (82560655085099 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (1143666995787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_45 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (1289479061481 / 1562500000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287338003293 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨45, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (1289479061481 / 1562500000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287338003293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_46 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (16498537679339 / 20000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (285917750171 / 12500000000000 : ℝ))
      (E := (cell12422 ⟨46, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (16498537679339 / 20000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (285917750171 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_47 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (3298349617661 / 4000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (71479562017 / 3125000000000 : ℝ))
      (E := (cell12422 ⟨47, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (3298349617661 / 4000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (71479562017 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_48 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (41212408020057 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (571837487837 / 25000000000000 : ℝ))
      (E := (cell12422 ⟨48, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (41212408020057 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (571837487837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_49 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (10298864395431 / 12500000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287353959023 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨49, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (10298864395431 / 12500000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287353959023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_50 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (82357037782661 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (1143679002869 / 50000000000000 : ℝ))
      (E := (cell12422 ⟨50, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (82357037782661 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (1143679002869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_51 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (8232318386903 / 10000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (228736197149 / 10000000000000 : ℝ))
      (E := (cell12422 ⟨51, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (8232318386903 / 10000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (228736197149 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_52 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (82289353393977 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (571841492971 / 25000000000000 : ℝ))
      (E := (cell12422 ⟨52, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (82289353393977 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (571841492971 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_53 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (20563886582267 / 25000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (71480312639 / 3125000000000 : ℝ))
      (E := (cell12422 ⟨53, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (20563886582267 / 25000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (71480312639 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_54 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (82221762646011 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287374007451 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨54, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (82221762646011 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287374007451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_55 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (41094001158327 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (571844494483 / 25000000000000 : ℝ))
      (E := (cell12422 ⟨55, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (41094001158327 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (571844494483 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_56 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (82154265312989 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287381971811 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨56, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (82154265312989 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287381971811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_57 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (41060275803573 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287385985779 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨57, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (41060275803573 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287385985779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_58 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (41043430585697 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (571847489293 / 25000000000000 : ℝ))
      (E := (cell12422 ⟨58, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (41043430585697 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (571847489293 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_59 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (41026596989071 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (91495760021 / 4000000000000 : ℝ))
      (E := (cell12422 ⟨59, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (41026596989071 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (91495760021 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12423_40 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (10337108684643 / 12500000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (228718295077 / 10000000000000 : ℝ))
      (E := (cell12423 ⟨40, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (10337108684643 / 12500000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (228718295077 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_41 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (10332847486877 / 12500000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287186928817 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨41, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (10332847486877 / 12500000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287186928817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_42 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (16525742808681 / 20000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143595477749 / 50000000000000 : ℝ))
      (E := (cell12423 ⟨42, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (16525742808681 / 20000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143595477749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_43 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (82594671892403 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287194912919 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨43, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (82594671892403 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287194912919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_44 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (82560653412257 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287198918033 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨44, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (82560653412257 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287198918033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_45 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (41263329286681 / 50000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1829762329 / 80000000000 : ℝ))
      (E := (cell12423 ⟨45, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (41263329286681 / 50000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1829762329 / 80000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_46 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (82492687346263 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (285900868799 / 12500000000000 : ℝ))
      (E := (cell12423 ⟨46, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (82492687346263 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (285900868799 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_47 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (82458739701653 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143605458251 / 50000000000000 : ℝ))
      (E := (cell12423 ⟨47, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (82458739701653 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143605458251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_48 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (41212407805187 / 50000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (571803731463 / 25000000000000 : ℝ))
      (E := (cell12423 ⟨48, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (41212407805187 / 50000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (571803731463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_49 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (82390915043413 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287218917893 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨49, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (82390915043413 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287218917893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_50 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (82357037971903 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143611474839 / 50000000000000 : ℝ))
      (E := (cell12423 ⟨50, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (82357037971903 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143611474839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_51 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (20580796091781 / 25000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (5718067253 / 250000000000 : ℝ))
      (E := (cell12423 ⟨51, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (20580796091781 / 25000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (5718067253 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_52 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (82289354200497 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287230947069 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨52, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (82289354200497 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287230947069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_53 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (82255547443589 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (457446981561 / 20000000000000 : ℝ))
      (E := (cell12423 ⟨53, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (82255547443589 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (457446981561 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_54 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (82221764068109 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287238898683 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨54, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (82221764068109 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287238898683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_55 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (41094002022953 / 50000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (228724291681 / 10000000000000 : ℝ))
      (E := (cell12423 ⟨55, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (41094002022953 / 50000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (228724291681 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_56 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (20538566837243 / 25000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143623449993 / 50000000000000 : ℝ))
      (E := (cell12423 ⟨56, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (20538566837243 / 25000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143623449993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_57 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (82120553949439 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (571812725987 / 25000000000000 : ℝ))
      (E := (cell12423 ⟨57, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (82120553949439 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (571812725987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_58 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (10260857977447 / 12500000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (285906865647 / 12500000000000 : ℝ))
      (E := (cell12423 ⟨58, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (10260857977447 / 12500000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (285906865647 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_59 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (5128324808237 / 6250000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (285907362597 / 12500000000000 : ℝ))
      (E := (cell12423 ⟨59, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (5128324808237 / 6250000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (285907362597 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12424_40 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (16539373311051 / 20000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143523977431 / 50000000000000 : ℝ))
      (E := (cell12424 ⟨40, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (16539373311051 / 20000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143523977431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_41 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (20665694321559 / 25000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (35735186119 / 1562500000000 : ℝ))
      (E := (cell12424 ⟨41, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (20665694321559 / 25000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (35735186119 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_42 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (826287117473 / 1000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143527958857 / 50000000000000 : ℝ))
      (E := (cell12424 ⟨42, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (826287117473 / 1000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143527958857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_43 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (41297334954271 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (45741198281 / 2000000000000 : ℝ))
      (E := (cell12424 ⟨43, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (41297334954271 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (45741198281 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_44 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (5160040733763 / 6250000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287063900019 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨44, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (5160040733763 / 6250000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287063900019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_45 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (41263328606347 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (571766983409 / 25000000000000 : ℝ))
      (E := (cell12424 ⟨45, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (41263328606347 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (571766983409 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_46 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (41246343148273 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287071955069 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨46, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (41246343148273 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287071955069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_47 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (82458738962459 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (142942244011 / 6250000000000 : ℝ))
      (E := (cell12424 ⟨47, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (82458738962459 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (142942244011 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_48 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (82424815181273 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (571769974307 / 25000000000000 : ℝ))
      (E := (cell12424 ⟨48, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (82424815181273 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (571769974307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_49 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (41195457461989 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143541966303 / 50000000000000 : ℝ))
      (E := (cell12424 ⟨49, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (41195457461989 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143541966303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_50 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (20589259540427 / 25000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287087949521 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨50, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (20589259540427 / 25000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287087949521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_51 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (41161592432871 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287091945857 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨51, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (41161592432871 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287091945857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_52 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (82289355007503 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143547959641 / 50000000000000 : ℝ))
      (E := (cell12424 ⟨52, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (82289355007503 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143547959641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_53 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (41127774279279 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287099926281 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨53, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (41127774279279 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287099926281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_54 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (82221765490617 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287103905119 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨54, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (82221765490617 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287103905119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_55 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (8218800577553 / 10000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143553955953 / 50000000000000 : ℝ))
      (E := (cell12424 ⟨55, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (8218800577553 / 10000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143553955953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_56 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (8215426938529 / 10000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287111943537 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨56, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (8215426938529 / 10000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287111943537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_57 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (20530139073007 / 25000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (114355796879 / 5000000000000 : ℝ))
      (E := (cell12424 ⟨57, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (20530139073007 / 25000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (114355796879 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_58 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (16417373293603 / 20000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287119949587 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨58, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (16417373293603 / 20000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287119949587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_59 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (41026599942831 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287123916661 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨59, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (41026599942831 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287123916661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

end BstLean.Part268
