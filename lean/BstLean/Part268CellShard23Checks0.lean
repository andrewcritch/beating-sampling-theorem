import BstLean.Part268CellShard23Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12925_0 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (84072645664779 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224640718499 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨0, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (84072645664779 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224640718499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_1 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (21009435427643 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (444928950721 / 20000000000000 : ℝ))
      (E := (cell12925 ⟨1, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (21009435427643 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (444928950721 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_2 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (21000715647563 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (111232437511 / 5000000000000 : ℝ))
      (E := (cell12925 ⟨2, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (21000715647563 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (111232437511 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_3 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (83968008267539 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224652716763 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨3, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (83968008267539 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224652716763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_4 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (83933178706343 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (556164179831 / 25000000000000 : ℝ))
      (E := (cell12925 ⟨4, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (83933178706343 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (556164179831 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_5 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (20974593467691 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224660765881 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨5, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (20974593467691 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224660765881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_6 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (20965898431273 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (139041546763 / 6250000000000 : ℝ))
      (E := (cell12925 ⟨6, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (20965898431273 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (139041546763 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_7 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (41914419116901 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224668731631 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨7, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (41914419116901 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224668731631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_8 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (20948526840389 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (444934556263 / 20000000000000 : ℝ))
      (E := (cell12925 ⟨8, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (20948526840389 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (444934556263 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_9 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (83759401073199 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224676788141 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨9, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (83759401073199 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224676788141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_10 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (83724719333761 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (556170189671 / 25000000000000 : ℝ))
      (E := (cell12925 ⟨10, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (83724719333761 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (556170189671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_11 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (41845031054227 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (1112342378679 / 50000000000000 : ℝ))
      (E := (cell12925 ⟨11, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (41845031054227 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (1112342378679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_12 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (5228464335167 / 6250000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (222468879031 / 10000000000000 : ℝ))
      (E := (cell12925 ⟨12, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (5228464335167 / 6250000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (222468879031 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_13 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (41810410530993 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (556173201327 / 25000000000000 : ℝ))
      (E := (cell12925 ⟨13, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (41810410530993 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (556173201327 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_14 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (1671724743443 / 2000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (444939361587 / 20000000000000 : ℝ))
      (E := (cell12925 ⟨14, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (1671724743443 / 2000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (444939361587 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_15 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (83551677659091 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224700803533 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨15, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (83551677659091 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224700803533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_16 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (20879285622229 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (5561761993 / 250000000000 : ℝ))
      (E := (cell12925 ⟨16, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (20879285622229 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (5561761993 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_17 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (41741315813953 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (222470879379 / 10000000000000 : ℝ))
      (E := (cell12925 ⟨17, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (41741315813953 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (222470879379 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_18 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (16689629008503 / 20000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224712797919 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨18, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (16689629008503 / 20000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224712797919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_19 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (41706841349687 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224716813957 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨19, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (41706841349687 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224716813957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12926_0 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (4203631552973 / 5000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224524659869 / 100000000000000 : ℝ))
      (E := (cell12926 ⟨0, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (4203631552973 / 5000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224524659869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_1 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (42018863708367 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224528672827 / 100000000000000 : ℝ))
      (E := (cell12926 ⟨1, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (42018863708367 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224528672827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_2 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (2625089018983 / 3125000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224532648007 / 100000000000000 : ℝ))
      (E := (cell12926 ⟨2, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (2625089018983 / 3125000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224532648007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_3 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (41983997297673 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (556134162933 / 25000000000000 : ℝ))
      (E := (cell12926 ⟨3, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (41983997297673 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (556134162933 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_4 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (16786633068863 / 20000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112270346117 / 50000000000000 : ℝ))
      (E := (cell12926 ⟨4, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (16786633068863 / 20000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112270346117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_5 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (41949180409233 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (222454466159 / 10000000000000 : ℝ))
      (E := (cell12926 ⟨5, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (41949180409233 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (222454466159 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_6 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (41931790491043 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (34758573177 / 1562500000000 : ℝ))
      (E := (cell12926 ⟨6, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (41931790491043 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (34758573177 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_7 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (41914412899827 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224552706917 / 100000000000000 : ℝ))
      (E := (cell12926 ⟨7, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (41914412899827 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224552706917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_8 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (83794095235831 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (444911336297 / 20000000000000 : ℝ))
      (E := (cell12926 ⟨8, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (83794095235831 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (444911336297 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_9 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (10469923656933 / 12500000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (22245606719 / 1000000000000 : ℝ))
      (E := (cell12926 ⟨9, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (10469923656933 / 12500000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (22245606719 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_10 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (16744941564717 / 20000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112282342401 / 50000000000000 : ℝ))
      (E := (cell12926 ⟨10, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (16744941564717 / 20000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112282342401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_11 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (41845025452703 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (4449137337 / 200000000000 : ℝ))
      (E := (cell12926 ⟨11, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (41845025452703 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (4449137337 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_12 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (1045692730829 / 1250000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224572687183 / 100000000000000 : ℝ))
      (E := (cell12926 ⟨12, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (1045692730829 / 1250000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224572687183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_13 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (41810405235951 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112288344307 / 50000000000000 : ℝ))
      (E := (cell12926 ⟨13, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (41810405235951 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112288344307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_14 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (16717245377581 / 20000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112290368269 / 50000000000000 : ℝ))
      (E := (cell12926 ⟨14, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (16717245377581 / 20000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112290368269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_15 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (83551667680257 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (27807309 / 1250000000 : ℝ))
      (E := (cell12926 ⟨15, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (83551667680257 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (27807309 / 1250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_16 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (83517132815067 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (278073587779 / 12500000000000 : ℝ))
      (E := (cell12926 ⟨16, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (83517132815067 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (278073587779 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_17 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (16696524451723 / 20000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (27807409329 / 1250000000000 : ℝ))
      (E := (cell12926 ⟨17, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (16696524451723 / 20000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (27807409329 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_18 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (83448135977359 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224596740437 / 100000000000000 : ℝ))
      (E := (cell12926 ⟨18, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (83448135977359 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224596740437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_19 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (83413673937927 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112300373583 / 50000000000000 : ℝ))
      (E := (cell12926 ⟨19, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (83413673937927 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112300373583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12927_0 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (84072616456403 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112204298389 / 50000000000000 : ℝ))
      (E := (cell12927 ⟨0, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (84072616456403 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112204298389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_1 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (42018856562561 / 50000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (278051573453 / 12500000000000 : ℝ))
      (E := (cell12927 ⟨1, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (42018856562561 / 50000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (278051573453 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_2 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (84002834626849 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224416599287 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨2, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (84002834626849 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224416599287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_3 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (16793596185061 / 20000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (444884128051 / 20000000000000 : ℝ))
      (E := (cell12927 ⟨3, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (16793596185061 / 20000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (444884128051 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_4 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (41966575992201 / 50000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (556106150727 / 25000000000000 : ℝ))
      (E := (cell12927 ⟨4, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (41966575992201 / 50000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (556106150727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_5 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (20974586942061 / 25000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112214305489 / 50000000000000 : ℝ))
      (E := (cell12927 ⟨5, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (20974586942061 / 25000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112214305489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_6 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (524147301507 / 625000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112216307107 / 50000000000000 : ℝ))
      (E := (cell12927 ⟨6, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (524147301507 / 625000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112216307107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_7 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (20957203341877 / 25000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224436620013 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨7, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (20957203341877 / 25000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224436620013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_8 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (10474260389009 / 12500000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112220317759 / 50000000000000 : ℝ))
      (E := (cell12927 ⟨8, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (10474260389009 / 12500000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112220317759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_9 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (4187968871983 / 5000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224444609579 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨9, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (4187968871983 / 5000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224444609579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_10 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (41862348157651 / 50000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (278056083113 / 12500000000000 : ℝ))
      (E := (cell12927 ⟨10, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (41862348157651 / 50000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (278056083113 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_11 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (83690039704213 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224452633687 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨11, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (83690039704213 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224452633687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_12 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (20913851892947 / 25000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (27805707977 / 1250000000000 : ℝ))
      (E := (cell12927 ⟨12, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (20913851892947 / 25000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (27805707977 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_13 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (83620799883601 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112230313043 / 50000000000000 : ℝ))
      (E := (cell12927 ⟨13, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (83620799883601 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112230313043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_14 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (41793108302703 / 50000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224464661209 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨14, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (41793108302703 / 50000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224464661209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_15 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (83551657703133 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (556117172689 / 25000000000000 : ℝ))
      (E := (cell12927 ⟨15, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (83551657703133 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (556117172689 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_16 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (83517123142891 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112236330807 / 50000000000000 : ℝ))
      (E := (cell12927 ⟨16, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (83517123142891 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112236330807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_17 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (41741306445481 / 50000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (556119173757 / 25000000000000 : ℝ))
      (E := (cell12927 ⟨17, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (41741306445481 / 50000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (556119173757 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_18 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (83448126913803 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224480679173 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨18, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (83448126913803 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224480679173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_19 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (16682733035609 / 20000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224484676627 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨19, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (16682733035609 / 20000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224484676627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12928_0 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (84072601855609 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112146293529 / 50000000000000 : ℝ))
      (E := (cell12928 ⟨0, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (84072601855609 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112146293529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_1 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (16807539767147 / 20000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224296613711 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨1, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (16807539767147 / 20000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224296613711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_2 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (84002820648429 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224300604063 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨2, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (84002820648429 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224300604063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_3 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (41983983628707 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224304566529 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨3, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (41983983628707 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224304566529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_4 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (41966569313301 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2780385709 / 125000000000 : ℝ))
      (E := (cell12928 ⟨4, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (41966569313301 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2780385709 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_5 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (83898334720099 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556078153511 / 25000000000000 : ℝ))
      (E := (cell12928 ⟨5, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (83898334720099 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556078153511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_6 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (41931777751097 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (55607914971 / 2500000000000 : ℝ))
      (E := (cell12928 ⟨6, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (41931777751097 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (55607914971 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_7 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (41914400468683 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556080146727 / 25000000000000 : ℝ))
      (E := (cell12928 ⟨7, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (41914400468683 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556080146727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_8 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (2094851774757 / 2500000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224324585391 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨8, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (2094851774757 / 2500000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224324585391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_9 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (10469920703223 / 12500000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224328601183 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨9, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (10469920703223 / 12500000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224328601183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_10 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (5232792800557 / 6250000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556083160231 / 25000000000000 : ℝ))
      (E := (cell12928 ⟨10, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (5232792800557 / 6250000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556083160231 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_11 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (83690028504877 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224336594829 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨11, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (83690028504877 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224336594829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_12 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (3346215867163 / 4000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556085160811 / 25000000000000 : ℝ))
      (E := (cell12928 ⟨12, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (3346215867163 / 4000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556085160811 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_13 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (83620789297083 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (88973784709 / 4000000000000 : ℝ))
      (E := (cell12928 ⟨13, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (83620789297083 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (88973784709 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_14 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (83586206324653 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556087160027 / 25000000000000 : ℝ))
      (E := (cell12928 ⟨14, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (83586206324653 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556087160027 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_15 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (83551647727719 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (444870531523 / 20000000000000 : ℝ))
      (E := (cell12928 ⟨15, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (83551647727719 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (444870531523 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_16 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (83517113472389 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224356617137 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨16, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (83517113472389 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224356617137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_17 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (41741301762473 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (444872127983 / 20000000000000 : ℝ))
      (E := (cell12928 ⟨17, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (41741301762473 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (444872127983 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_18 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (83448117851849 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112182336189 / 50000000000000 : ℝ))
      (E := (cell12928 ⟨18, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (83448117851849 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112182336189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_19 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (83413656419727 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (111218433031 / 5000000000000 : ℝ))
      (E := (cell12928 ⟨19, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (83413656419727 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (111218433031 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12929_0 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (21018146814269 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224176572879 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨0, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (21018146814269 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224176572879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_1 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (21009421137143 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224180577521 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨1, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (21009421137143 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224180577521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_2 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (21000701668049 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (444836920891 / 20000000000000 : ℝ))
      (E := (cell12929 ⟨2, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (21000701668049 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (444836920891 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_3 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (83967953591673 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (278023575533 / 12500000000000 : ℝ))
      (E := (cell12929 ⟨3, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (83967953591673 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (278023575533 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_4 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (20983281317729 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224192585109 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨4, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (20983281317729 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224192585109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_5 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (83898321674029 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224196612843 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨5, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (83898321674029 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224196612843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_6 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (41931771382653 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556050144809 / 25000000000000 : ℝ))
      (E := (cell12929 ⟨6, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (41931771382653 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556050144809 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_7 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (3353151540369 / 4000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224204607607 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨7, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (3353151540369 / 4000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224204607607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_8 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (20948514717613 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (222420858913 / 10000000000000 : ℝ))
      (E := (cell12929 ⟨8, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (20948514717613 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (222420858913 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_9 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (83759353813837 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556053147167 / 25000000000000 : ℝ))
      (E := (cell12929 ⟨9, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (83759353813837 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556053147167 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_10 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (83724673304413 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (271510817 / 12207031250 : ℝ))
      (E := (cell12929 ⟨10, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (83724673304413 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (271510817 / 12207031250 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_11 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (16738003461479 / 20000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224220610019 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨11, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (16738003461479 / 20000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224220610019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_12 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (83655385788181 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112112322161 / 50000000000000 : ℝ))
      (E := (cell12929 ⟨12, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (83655385788181 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112112322161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_13 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (41810389356173 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224228605397 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨13, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (41810389356173 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224228605397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_14 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (41793098022823 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (88969304603 / 4000000000000 : ℝ))
      (E := (cell12929 ⟨14, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (41793098022823 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (88969304603 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_15 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (41775818877007 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112118310291 / 50000000000000 : ℝ))
      (E := (cell12929 ⟨15, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (41775818877007 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112118310291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_16 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (83517103803559 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224240627011 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨16, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (83517103803559 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224240627011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_17 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (41741297080283 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (444848927843 / 20000000000000 : ℝ))
      (E := (cell12929 ⟨17, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (41741297080283 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (444848927843 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_18 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (41724054395747 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112124330901 / 50000000000000 : ℝ))
      (E := (cell12929 ⟨18, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (41724054395747 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112124330901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_19 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (41706823831487 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556063160217 / 25000000000000 : ℝ))
      (E := (cell12929 ⟨19, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (41706823831487 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556063160217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12930_0 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (21018143165201 / 25000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112030306037 / 50000000000000 : ℝ))
      (E := (cell12930 ⟨0, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (21018143165201 / 25000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112030306037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_1 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (84037670263633 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112032297383 / 50000000000000 : ℝ))
      (E := (cell12930 ⟨1, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (84037670263633 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112032297383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_2 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (1680055853963 / 2000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (444813720093 / 20000000000000 : ℝ))
      (E := (cell12930 ⟨2, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (1680055853963 / 2000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (444813720093 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_3 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (83967939928081 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (278009079707 / 12500000000000 : ℝ))
      (E := (cell12930 ⟨3, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (83967939928081 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (278009079707 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_4 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (83933111917341 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112038299357 / 50000000000000 : ℝ))
      (E := (cell12930 ⟨4, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (83933111917341 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112038299357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_5 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (16779661726007 / 20000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (556020151843 / 25000000000000 : ℝ))
      (E := (cell12930 ⟨5, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (16779661726007 / 20000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (556020151843 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_6 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (83863530030457 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224084613373 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨6, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (83863530030457 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224084613373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_7 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (41914388041543 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224088624113 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨7, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (41914388041543 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224088624113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_8 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (8379404675259 / 10000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (556023161683 / 25000000000000 : ℝ))
      (E := (cell12930 ⟨8, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (8379404675259 / 10000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (556023161683 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_9 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (41879671001909 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224096630079 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨9, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (41879671001909 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224096630079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_10 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (41862330900903 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (222410063879 / 10000000000000 : ℝ))
      (E := (cell12930 ⟨10, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (41862330900903 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (222410063879 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_11 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (10461250763971 / 12500000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224104621167 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨11, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (10461250763971 / 12500000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224104621167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_12 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (16731074979821 / 20000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (444821728279 / 20000000000000 : ℝ))
      (E := (cell12930 ⟨12, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (16731074979821 / 20000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (444821728279 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_13 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (83620768129391 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224112647237 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨13, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (83620768129391 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224112647237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_14 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (1306034152631 / 1562500000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224116644273 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨14, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (1306034152631 / 1562500000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224116644273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_15 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (41775813891009 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224120637839 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨15, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (41775813891009 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224120637839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_16 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (41758547068201 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224124691237 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨16, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (41758547068201 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224124691237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_17 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (83482584797823 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (88965147717 / 4000000000000 : ℝ))
      (E := (cell12930 ⟨17, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (83482584797823 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (88965147717 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_18 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (83448099732739 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112066352849 / 50000000000000 : ℝ))
      (E := (cell12930 ⟨18, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (83448099732739 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112066352849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_19 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (10426704863473 / 12500000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (34752135557 / 1562500000000 : ℝ))
      (E := (cell12930 ⟨19, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (10426704863473 / 12500000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (34752135557 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12931_0 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (84072558066793 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (555986161703 / 25000000000000 : ℝ))
      (E := (cell12931 ⟨0, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (84072558066793 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (555986161703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_1 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (84037655980917 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2223948665449 / 100000000000000 : ℝ))
      (E := (cell12931 ⟨1, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (84037655980917 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2223948665449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_2 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (8400277872629 / 10000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1111976324987 / 50000000000000 : ℝ))
      (E := (cell12931 ⟨2, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (8400277872629 / 10000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1111976324987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_3 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (83967926266639 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (138997291669 / 6250000000000 : ℝ))
      (E := (cell12931 ⟨3, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (83967926266639 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (138997291669 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_4 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (83933098565879 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (111198033297 / 5000000000000 : ℝ))
      (E := (cell12931 ⟨4, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (83933098565879 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (111198033297 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_5 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (83898295588117 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (69498895487 / 3125000000000 : ℝ))
      (E := (cell12931 ⟨5, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (83898295588117 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (69498895487 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_6 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (41931758648823 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (277996087657 / 12500000000000 : ℝ))
      (E := (cell12931 ⟨6, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (41931758648823 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (277996087657 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_7 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (83828763658949 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (88958907777 / 4000000000000 : ℝ))
      (E := (cell12931 ⟨7, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (83828763658949 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (88958907777 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_8 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (20948508659173 / 25000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1111988350091 / 50000000000000 : ℝ))
      (E := (cell12931 ⟨8, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (20948508659173 / 25000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1111988350091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_9 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (83759330195727 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (17791845339 / 800000000000 : ℝ))
      (E := (cell12931 ⟨9, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (83759330195727 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (17791845339 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_10 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (83724650301089 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1111992359353 / 50000000000000 : ℝ))
      (E := (cell12931 ⟨10, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (83724650301089 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1111992359353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_11 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (20922498729499 / 25000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (555997171591 / 25000000000000 : ℝ))
      (E := (cell12931 ⟨11, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (20922498729499 / 25000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (555997171591 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_12 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (41827682005923 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (111199634629 / 5000000000000 : ℝ))
      (E := (cell12931 ⟨12, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (41827682005923 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (111199634629 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_13 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (41810378774109 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (277999585639 / 12500000000000 : ℝ))
      (E := (cell12931 ⟨13, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (41810378774109 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (277999585639 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_14 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (83586175492867 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224000727703 / 100000000000000 : ℝ))
      (E := (cell12931 ⟨14, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (83586175492867 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224000727703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_15 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (8355161781173 / 10000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (222400470939 / 10000000000000 : ℝ))
      (E := (cell12931 ⟨15, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (8355161781173 / 10000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (222400470939 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_16 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (83517084470917 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1112004346701 / 50000000000000 : ℝ))
      (E := (cell12931 ⟨16, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (83517084470917 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1112004346701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_17 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (16696515087343 / 20000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (111200637141 / 5000000000000 : ℝ))
      (E := (cell12931 ⟨17, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (16696515087343 / 20000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (111200637141 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_18 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (83448090675583 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224016745817 / 100000000000000 : ℝ))
      (E := (cell12931 ⟨18, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (83448090675583 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224016745817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_19 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (83413630154157 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (17375161771 / 781250000000 : ℝ))
      (E := (cell12931 ⟨19, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (83413630154157 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (17375161771 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12932_0 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (84072543475041 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223828734927 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨0, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (84072543475041 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223828734927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_1 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (10504705212553 / 12500000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111916365857 / 50000000000000 : ℝ))
      (E := (cell12932 ⟨1, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (10504705212553 / 12500000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111916365857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_2 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (10500345594577 / 12500000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111918376491 / 50000000000000 : ℝ))
      (E := (cell12932 ⟨2, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (10500345594577 / 12500000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111918376491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_3 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (16793582521469 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223840749313 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨3, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (16793582521469 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223840749313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_4 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (5245817826033 / 6250000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111922364431 / 50000000000000 : ℝ))
      (E := (cell12932 ⟨4, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (5245817826033 / 6250000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111922364431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_5 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (5243642659267 / 6250000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (55596218937 / 2500000000000 : ℝ))
      (E := (cell12932 ⟨5, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (5243642659267 / 6250000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (55596218937 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_6 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (83863504566873 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (444770545387 / 20000000000000 : ℝ))
      (E := (cell12932 ⟨6, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (83863504566873 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (444770545387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_7 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (20957187809203 / 25000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (444771352109 / 20000000000000 : ℝ))
      (E := (cell12932 ⟨7, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (20957187809203 / 25000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (444771352109 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_8 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (41897011261379 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111930374739 / 50000000000000 : ℝ))
      (E := (cell12932 ⟨8, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (41897011261379 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111930374739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_9 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (83759318389563 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111932379299 / 50000000000000 : ℝ))
      (E := (cell12932 ⟨9, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (83759318389563 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111932379299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_10 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (10465579850283 / 12500000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223868794541 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨10, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (10465579850283 / 12500000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223868794541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_11 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (41844991863039 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223872747519 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨11, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (41844991863039 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223872747519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_12 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (16731070625281 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111938398937 / 50000000000000 : ℝ))
      (E := (cell12932 ⟨12, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (16731070625281 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111938398937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_13 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (3344829878753 / 4000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111940388579 / 50000000000000 : ℝ))
      (E := (cell12932 ⟨13, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (3344829878753 / 4000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111940388579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_14 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (16717233043819 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (555971201801 / 25000000000000 : ℝ))
      (E := (cell12932 ⟨14, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (16717233043819 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (555971201801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_15 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (1671032156863 / 2000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223888777049 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨15, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (1671032156863 / 2000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223888777049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_16 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (1304954293861 / 1562500000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223892808127 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨16, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (1304954293861 / 1562500000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223892808127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_17 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (41741283038621 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223896788899 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨17, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (41741283038621 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223896788899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_18 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (83448081620027 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111950391077 / 50000000000000 : ℝ))
      (E := (cell12932 ⟨18, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (83448081620027 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111950391077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_19 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (83413621402093 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223904792261 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨19, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (83413621402093 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223904792261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12933_0 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (84072528885549 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223712818587 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨0, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (84072528885549 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223712818587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_1 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (84037627422153 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111858425709 / 50000000000000 : ℝ))
      (E := (cell12933 ⟨1, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (84037627422153 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111858425709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_2 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (84002750789127 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (555930212903 / 25000000000000 : ℝ))
      (E := (cell12933 ⟨2, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (84002750789127 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (555930212903 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_3 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (83967898950199 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223724827581 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨3, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (83967898950199 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223724827581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_4 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (10491633983661 / 12500000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223728845407 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨4, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (10491633983661 / 12500000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223728845407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_5 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (41949134755251 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (222373285511 / 10000000000000 : ℝ))
      (E := (cell12933 ⟨5, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (41949134755251 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (222373285511 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_6 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (83863491838137 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111868432167 / 50000000000000 : ℝ))
      (E := (cell12933 ⟨6, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (83863491838137 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111868432167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_7 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (20957184704169 / 25000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (277967610059 / 12500000000000 : ℝ))
      (E := (cell12933 ⟨7, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (20957184704169 / 25000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (277967610059 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_8 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (83794010410787 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223744852643 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨8, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (83794010410787 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223744852643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_9 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (41879653292663 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223748845707 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨9, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (41879653292663 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223748845707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_10 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (5232789206583 / 6250000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111876433151 / 50000000000000 : ℝ))
      (E := (cell12933 ⟨10, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (5232789206583 / 6250000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111876433151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_11 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (83689972536013 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223756862727 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨11, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (83689972536013 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223756862727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_12 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (83655342242781 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111880449583 / 50000000000000 : ℝ))
      (E := (cell12933 ⟨12, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (83655342242781 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111880449583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_13 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (20905184097803 / 25000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223764865241 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨13, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (20905184097803 / 25000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223764865241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_14 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (41793077473533 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223768882779 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨14, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (41793077473533 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223768882779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_15 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (41775798938139 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111886449501 / 50000000000000 : ℝ))
      (E := (cell12933 ⟨15, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (41775798938139 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111886449501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_16 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (83517065144961 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223776919001 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨16, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (83517065144961 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223776919001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_17 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (20870639179851 / 25000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (138986305587 / 6250000000000 : ℝ))
      (E := (cell12933 ⟨17, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (20870639179851 / 25000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (138986305587 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_18 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (83448072566069 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111892465611 / 50000000000000 : ℝ))
      (E := (cell12933 ⟨18, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (83448072566069 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111892465611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_19 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (83413612651591 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (555947233093 / 25000000000000 : ℝ))
      (E := (cell12933 ⟨19, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (83413612651591 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (555947233093 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12934_0 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (21018128574579 / 25000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111798477813 / 50000000000000 : ℝ))
      (E := (cell12934 ⟨0, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (21018128574579 / 25000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111798477813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_1 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (84037613146103 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223600966707 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨1, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (84037613146103 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223600966707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_2 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (42001368411911 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223604945863 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨2, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (42001368411911 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223604945863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_3 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (83967885295201 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (555902239853 / 25000000000000 : ℝ))
      (E := (cell12934 ⟨3, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (83967885295201 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (555902239853 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_4 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (83933058524159 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (44472259153 / 2000000000000 : ℝ))
      (E := (cell12934 ⟨4, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (83933058524159 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (44472259153 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_5 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (41949128237403 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (88944680257 / 4000000000000 : ℝ))
      (E := (cell12934 ⟨5, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (41949128237403 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (88944680257 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_6 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (41931739555719 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223620997507 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨6, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (41931739555719 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223620997507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_7 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (83828726398539 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (555906249053 / 25000000000000 : ℝ))
      (E := (cell12934 ⟨7, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (83828726398539 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (555906249053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_8 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (4189699915039 / 5000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223629009677 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨8, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (4189699915039 / 5000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223629009677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_9 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (16751858956603 / 20000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111816493373 / 50000000000000 : ℝ))
      (E := (cell12934 ⟨9, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (16751858956603 / 20000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111816493373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_10 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (41862307905141 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223636992053 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨10, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (41862307905141 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223636992053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_11 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (83689961347801 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (277955121737 / 12500000000000 : ℝ))
      (E := (cell12934 ⟨11, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (83689961347801 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (277955121737 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_12 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (83655331360973 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223644996459 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨12, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (83655331360973 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223644996459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_13 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (4181036290769 / 5000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (277956125937 / 12500000000000 : ℝ))
      (E := (cell12934 ⟨13, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (4181036290769 / 5000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (277956125937 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_14 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (83586144676781 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (555913253147 / 25000000000000 : ℝ))
      (E := (cell12934 ⟨14, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (83586144676781 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (555913253147 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_15 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (83551587911113 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111828508533 / 50000000000000 : ℝ))
      (E := (cell12934 ⟨15, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (83551587911113 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111828508533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_16 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (8351705548449 / 10000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111830513011 / 50000000000000 : ℝ))
      (E := (cell12934 ⟨16, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (8351705548449 / 10000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111830513011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_17 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (83482547363201 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111832522151 / 50000000000000 : ℝ))
      (E := (cell12934 ⟨17, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (83482547363201 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111832522151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_18 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (8344806351371 / 10000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111834509129 / 50000000000000 : ℝ))
      (E := (cell12934 ⟨18, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (8344806351371 / 10000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111834509129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_19 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (20853400975663 / 25000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (69489781577 / 3125000000000 : ℝ))
      (E := (cell12934 ⟨19, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (20853400975663 / 25000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (69489781577 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12935_0 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (84072499713341 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (555870272053 / 25000000000000 : ℝ))
      (E := (cell12935 ⟨0, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (84072499713341 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (555870272053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_1 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (3361503954891 / 4000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223485135437 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨1, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (3361503954891 / 4000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223485135437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_2 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (84002722860701 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223489093619 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨2, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (84002722860701 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223489093619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_3 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (1679357432847 / 2000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (277936643101 / 12500000000000 : ℝ))
      (E := (cell12935 ⟨3, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (1679357432847 / 2000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (277936643101 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_4 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (4196652259057 / 5000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223497123519 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨4, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (4196652259057 / 5000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223497123519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_5 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (41949121720591 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (55587528837 / 2500000000000 : ℝ))
      (E := (cell12935 ⟨5, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (41949121720591 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (55587528837 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_6 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (41931733193387 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (277938140807 / 12500000000000 : ℝ))
      (E := (cell12935 ⟨6, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (41931733193387 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (277938140807 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_7 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (41914356991201 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (6948466143 / 312500000000 : ℝ))
      (E := (cell12935 ⟨7, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (41914356991201 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (6948466143 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_8 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (16758797238547 / 20000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223513162561 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨8, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (16758797238547 / 20000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223513162561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_9 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (8375928298263 / 10000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223517123673 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨9, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (8375928298263 / 10000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223517123673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_10 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (669796834537 / 800000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111760585899 / 50000000000000 : ℝ))
      (E := (cell12935 ⟨10, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (669796834537 / 800000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111760585899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_11 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (41844975080721 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223525139119 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨11, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (41844975080721 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223525139119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_12 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (41827660240491 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (277941143483 / 12500000000000 : ℝ))
      (E := (cell12935 ⟨12, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (41827660240491 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (277941143483 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_13 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (83620715241327 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (222353314579 / 10000000000000 : ℝ))
      (E := (cell12935 ⟨13, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (83620715241327 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (222353314579 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_14 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (83586134408239 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (277942142309 / 12500000000000 : ℝ))
      (E := (cell12935 ⟨14, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (83586134408239 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (277942142309 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_15 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (41775788973827 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (555885297357 / 25000000000000 : ℝ))
      (E := (cell12935 ⟨15, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (41775788973827 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (555885297357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_16 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (83517045825689 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223545187401 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨16, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (83517045825689 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223545187401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_17 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (10435317251079 / 12500000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223549195399 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨17, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (10435317251079 / 12500000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223549195399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_18 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (20862013615737 / 25000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223553159773 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨18, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (20862013615737 / 25000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223553159773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_19 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (41706797577637 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223557201373 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨19, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (41706797577637 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223557201373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12936_0 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (656816290083 / 781250000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (111168263709 / 5000000000000 : ℝ))
      (E := (cell12936 ⟨0, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (656816290083 / 781250000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (111168263709 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_1 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (84037584600667 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111684649877 / 50000000000000 : ℝ))
      (E := (cell12936 ⟨1, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (84037584600667 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111684649877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_2 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (21000677224941 / 25000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111686647439 / 50000000000000 : ℝ))
      (E := (cell12936 ⟨2, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (21000677224941 / 25000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111686647439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_3 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (16793571598329 / 20000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111688662933 / 50000000000000 : ℝ))
      (E := (cell12936 ⟨3, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (16793571598329 / 20000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111688662933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_4 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (8393303184023 / 10000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (69480665159 / 3125000000000 : ℝ))
      (E := (cell12936 ⟨4, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (8393303184023 / 10000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (69480665159 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_5 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (83898230409631 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223385296271 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨5, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (83898230409631 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223385296271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_6 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (83863453664147 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223389309153 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨6, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (83863453664147 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223389309153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_7 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (83828701568263 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223393331123 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨7, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (83828701568263 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223393331123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_8 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (20948493521663 / 25000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223397311297 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨8, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (20948493521663 / 25000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223397311297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_9 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (8375927118417 / 10000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111700657267 / 50000000000000 : ℝ))
      (E := (cell12936 ⟨9, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (8375927118417 / 10000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111700657267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_10 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (83724592825857 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (555851336867 / 25000000000000 : ℝ))
      (E := (cell12936 ⟨10, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (83724592825857 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (555851336867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_11 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (16737987795387 / 20000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (555852339599 / 25000000000000 : ℝ))
      (E := (cell12936 ⟨11, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (16737987795387 / 20000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (555852339599 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_12 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (41827654801403 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111706676693 / 50000000000000 : ℝ))
      (E := (cell12936 ⟨12, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (41827654801403 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111706676693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_13 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (83620704669053 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223417338261 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨13, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (83620704669053 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223417338261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_14 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (83586124141439 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111710659297 / 50000000000000 : ℝ))
      (E := (cell12936 ⟨14, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (83586124141439 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111710659297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_15 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (41775783992951 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223425357903 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨15, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (41775783992951 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223425357903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_16 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (83517036168557 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223429344931 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨16, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (83517036168557 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223429344931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_17 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (5217658040981 / 6250000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (555858335671 / 25000000000000 : ℝ))
      (E := (cell12936 ⟨17, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (5217658040981 / 6250000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (555858335671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_18 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (10431005676723 / 12500000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111718677883 / 50000000000000 : ℝ))
      (E := (cell12936 ⟨18, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (10431005676723 / 12500000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111718677883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_19 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (83413586409457 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (444688277709 / 20000000000000 : ℝ))
      (E := (cell12936 ⟨19, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (83413586409457 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (444688277709 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12937_0 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (21018117637541 / 25000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223249513531 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨0, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (21018117637541 / 25000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223249513531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_1 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (1050469629141 / 1250000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (444650703503 / 20000000000000 : ℝ))
      (E := (cell12937 ⟨1, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (1050469629141 / 1250000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (444650703503 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_2 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (8400269494101 / 10000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223257491763 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨2, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (8400269494101 / 10000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223257491763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_3 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (41983922171543 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223261502589 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨3, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (41983922171543 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223261502589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_4 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (83933018501429 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223265500287 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨4, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (83933018501429 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223265500287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_5 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (10487277172519 / 12500000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223269492753 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨5, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (10487277172519 / 12500000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223269492753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_6 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (16772688188711 / 20000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223273487627 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨6, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (16772688188711 / 20000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223273487627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_7 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (83828689156123 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (22232774923 / 1000000000000 : ℝ))
      (E := (cell12937 ⟨7, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (83828689156123 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (22232774923 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_8 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (83793961982531 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111640756953 / 50000000000000 : ℝ))
      (E := (cell12937 ⟨8, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (83793961982531 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111640756953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_9 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (20939814846909 / 25000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223285501283 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨9, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (20939814846909 / 25000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223285501283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_10 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (83724581336477 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223289519067 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨10, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (83724581336477 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223289519067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_11 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (83689927794279 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (555823378887 / 25000000000000 : ℝ))
      (E := (cell12937 ⟨11, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (83689927794279 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (555823378887 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_12 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (16731059745289 / 20000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223297554911 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨12, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (16731059745289 / 20000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223297554911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_13 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (41810347049279 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (222330152677 / 10000000000000 : ℝ))
      (E := (cell12937 ⟨13, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (41810347049279 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (222330152677 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_14 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (41793056938191 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223305552953 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨14, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (41793056938191 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223305552953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_15 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (16710311605171 / 20000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223309522493 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨15, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (16710311605171 / 20000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223309522493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_16 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (10439628314137 / 12500000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223313556819 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨16, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (10439628314137 / 12500000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223313556819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_17 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (41741259652197 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (555829386097 / 25000000000000 : ℝ))
      (E := (cell12937 ⟨17, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (41741259652197 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (555829386097 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_18 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (10431004545777 / 12500000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223321547987 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨18, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (10431004545777 / 12500000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223321547987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_19 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (83413577665201 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223325571979 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨19, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (83413577665201 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223325571979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12938_0 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (84072455971961 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223133748433 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨0, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (84072455971961 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223133748433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_1 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (5252347254007 / 6250000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (444627546173 / 20000000000000 : ℝ))
      (E := (cell12938 ⟨1, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (5252347254007 / 6250000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (444627546173 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_2 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (84002680984439 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (444628348431 / 20000000000000 : ℝ))
      (E := (cell12938 ⟨2, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (84002680984439 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (444628348431 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_3 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (83967830696673 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111572866439 / 50000000000000 : ℝ))
      (E := (cell12938 ⟨3, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (83967830696673 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111572866439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_4 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (83933005164737 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223149711187 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨4, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (83933005164737 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223149711187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_5 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (16779640870549 / 20000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (555788435731 / 25000000000000 : ℝ))
      (E := (cell12938 ⟨5, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (16779640870549 / 20000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (555788435731 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_6 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (83863428224997 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111578859927 / 50000000000000 : ℝ))
      (E := (cell12938 ⟨6, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (83863428224997 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111578859927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_7 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (83828676745981 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (277895220661 / 12500000000000 : ℝ))
      (E := (cell12938 ⟨7, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (83828676745981 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (277895220661 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_8 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (83793949880371 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (555791442597 / 25000000000000 : ℝ))
      (E := (cell12938 ⟨8, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (83793949880371 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (555791442597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_9 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (41879623796513 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (138948108873 / 6250000000000 : ℝ))
      (E := (cell12938 ⟨9, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (41879623796513 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (138948108873 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_10 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (16744913969797 / 20000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223173744661 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨10, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (16744913969797 / 20000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223173744661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_11 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (3347596664539 / 4000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223177784847 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨11, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (3347596664539 / 4000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223177784847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_12 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (83655287851899 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111590876219 / 50000000000000 : ℝ))
      (E := (cell12938 ⟨12, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (83655287851899 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111590876219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_13 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (83620683529841 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223185769459 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨13, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (83620683529841 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223185769459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_14 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (41793051806533 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223189783391 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨14, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (41793051806533 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223189783391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_15 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (41775774033757 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111596899783 / 50000000000000 : ℝ))
      (E := (cell12938 ⟨15, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (41775774033757 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111596899783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_16 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (83517016859303 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223197764861 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨16, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (83517016859303 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223197764861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_17 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (3339300398189 / 4000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223201800513 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨17, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (3339300398189 / 4000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223201800513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_18 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (41724013660123 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (17368795271 / 781250000000 : ℝ))
      (E := (cell12938 ⟨18, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (41724013660123 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (17368795271 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_19 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (41706784461253 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111604904977 / 50000000000000 : ℝ))
      (E := (cell12938 ⟨19, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (41706784461253 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111604904977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12939_0 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (42036220698007 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111508989443 / 50000000000000 : ℝ))
      (E := (cell12939 ⟨0, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (42036220698007 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111508989443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_1 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (21009385449791 / 25000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223021997661 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨1, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (21009385449791 / 25000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223021997661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_2 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (84002667030049 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (88921039527 / 4000000000000 : ℝ))
      (E := (cell12939 ⟨2, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (84002667030049 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (88921039527 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_3 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (20991954263101 / 25000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (444605991767 / 20000000000000 : ℝ))
      (E := (cell12939 ⟨3, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (20991954263101 / 25000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (444605991767 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_4 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (83932991830153 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111516987859 / 50000000000000 : ℝ))
      (E := (cell12939 ⟨4, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (83932991830153 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111516987859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_5 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (83898191327409 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223037988837 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨5, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (83898191327409 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223037988837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_6 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (41931707754237 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223042005833 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨6, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (41931707754237 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223042005833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_7 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (83828664337837 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111522988047 / 50000000000000 : ℝ))
      (E := (cell12939 ⟨7, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (83828664337837 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111522988047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_8 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (20948484445043 / 25000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (88922000909 / 4000000000000 : ℝ))
      (E := (cell12939 ⟨8, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (20948484445043 / 25000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (88922000909 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_9 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (83759235800339 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111526989273 / 50000000000000 : ℝ))
      (E := (cell12939 ⟨9, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (83759235800339 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111526989273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_10 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (83724558363381 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223058024251 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨10, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (83724558363381 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223058024251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_11 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (83689905434521 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (277882749003 / 12500000000000 : ℝ))
      (E := (cell12939 ⟨11, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (83689905434521 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (277882749003 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_12 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (83655276979167 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (444613200817 / 20000000000000 : ℝ))
      (E := (cell12939 ⟨12, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (83655276979167 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (444613200817 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_13 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (41810336481451 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223070008189 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨13, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (41810336481451 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223070008189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_14 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (20896523337873 / 25000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (555768502477 / 25000000000000 : ℝ))
      (E := (cell12939 ⟨14, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (20896523337873 / 25000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (555768502477 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_15 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (83551538110879 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (222307801457 / 10000000000000 : ℝ))
      (E := (cell12939 ⟨15, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (83551538110879 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (222307801457 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_16 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (83517007207179 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (8683914169 / 390625000000 : ℝ))
      (E := (cell12939 ⟨16, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (83517007207179 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (8683914169 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_17 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (2608828143959 / 3125000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (222308605283 / 10000000000000 : ℝ))
      (E := (cell12939 ⟨17, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (2608828143959 / 3125000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (222308605283 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_18 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (83448018275871 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111545018809 / 50000000000000 : ℝ))
      (E := (cell12939 ⟨18, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (83448018275871 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111545018809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_19 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (83413560181371 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (444618808839 / 20000000000000 : ℝ))
      (E := (cell12939 ⟨19, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (83413560181371 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (444618808839 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12940_0 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (84072426822323 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111451131363 / 50000000000000 : ℝ))
      (E := (cell12940 ⟨0, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (84072426822323 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111451131363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_1 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (42018763768217 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (138931641253 / 6250000000000 : ℝ))
      (E := (cell12940 ⟨1, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (42018763768217 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (138931641253 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_2 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (84002653077841 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (34732972341 / 1562500000000 : ℝ))
      (E := (cell12940 ⟨2, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (84002653077841 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (34732972341 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_3 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (83967803410281 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2222914238361 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨3, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (83967803410281 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2222914238361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_4 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (20983244624419 / 25000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111459117977 / 50000000000000 : ℝ))
      (E := (cell12940 ⟨4, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (20983244624419 / 25000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111459117977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_5 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (83898178304143 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (555730572111 / 25000000000000 : ℝ))
      (E := (cell12940 ⟨5, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (83898178304143 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (555730572111 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_6 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (81897854291 / 97656250000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111463143797 / 50000000000000 : ℝ))
      (E := (cell12940 ⟨6, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (81897854291 / 97656250000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111463143797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_7 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (83828651931689 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111465149357 / 50000000000000 : ℝ))
      (E := (cell12940 ⟨7, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (83828651931689 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111465149357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_8 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (83793925681933 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111467135459 / 50000000000000 : ℝ))
      (E := (cell12940 ⟨8, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (83793925681933 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111467135459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_9 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (83759224009577 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (111146913453 / 5000000000000 : ℝ))
      (E := (cell12940 ⟨9, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (83759224009577 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (111146913453 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_10 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (83724546879663 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111471149887 / 50000000000000 : ℝ))
      (E := (cell12940 ⟨10, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (83724546879663 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111471149887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_11 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (41844947128709 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2222946311349 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨11, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (41844947128709 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2222946311349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_12 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (83655266108249 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2222950309851 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨12, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (83655266108249 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2222950309851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_13 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (83620662397741 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2222954301099 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨13, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (83620662397741 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2222954301099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_14 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (83586083091659 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111479145333 / 50000000000000 : ℝ))
      (E := (cell12940 ⟨14, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (83586083091659 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111479145333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_15 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (83551528155947 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111481141939 / 50000000000000 : ℝ))
      (E := (cell12940 ⟨15, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (83551528155947 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111481141939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_16 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (20879249389181 / 25000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2222966285821 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨16, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (20879249389181 / 25000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2222966285821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_17 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (83482491260283 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111485150669 / 50000000000000 : ℝ))
      (E := (cell12940 ⟨17, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (83482491260283 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111485150669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_18 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (83448009233093 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (222297433503 / 10000000000000 : ℝ))
      (E := (cell12940 ⟨18, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (83448009233093 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (222297433503 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_19 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (20853387860449 / 25000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (111148916649 / 5000000000000 : ℝ))
      (E := (cell12940 ⟨19, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (20853387860449 / 25000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (111148916649 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12941_0 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (84072412250887 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222786542119 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨0, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (84072412250887 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222786542119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_1 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (42018756637961 / 50000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (555697643971 / 25000000000000 : ℝ))
      (E := (cell12941 ⟨1, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (42018756637961 / 50000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (555697643971 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_2 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (42001319563907 / 50000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222794582863 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨2, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (42001319563907 / 50000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222794582863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_3 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (83967789770301 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222798571459 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨3, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (83967789770301 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222798571459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_4 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (83932965167307 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111401274911 / 50000000000000 : ℝ))
      (E := (cell12941 ⟨4, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (83932965167307 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111401274911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_5 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (20974541320737 / 25000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222806583793 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨5, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (20974541320737 / 25000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222806583793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_6 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (10482923760191 / 12500000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111405282567 / 50000000000000 : ℝ))
      (E := (cell12941 ⟨6, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (10482923760191 / 12500000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111405282567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_7 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (41914319763769 / 50000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111407279577 / 50000000000000 : ℝ))
      (E := (cell12941 ⟨7, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (41914319763769 / 50000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111407279577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_8 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (41896956792827 / 50000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222818572987 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨8, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (41896956792827 / 50000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222818572987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_9 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (83759212220737 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222822555469 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨9, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (83759212220737 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222822555469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_10 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (10465566924729 / 12500000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222826571227 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨10, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (10465566924729 / 12500000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222826571227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_11 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (16737976616433 / 20000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (277853821069 / 12500000000000 : ℝ))
      (E := (cell12941 ⟨11, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (16737976616433 / 20000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (277853821069 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_12 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (10456906904893 / 12500000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (277854326453 / 12500000000000 : ℝ))
      (E := (cell12941 ⟨12, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (10456906904893 / 12500000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (277854326453 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_13 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (20905162958589 / 25000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111419295027 / 50000000000000 : ℝ))
      (E := (cell12941 ⟨13, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (20905162958589 / 25000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111419295027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_14 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (83586072833567 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (444568525133 / 20000000000000 : ℝ))
      (E := (cell12941 ⟨14, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (83586072833567 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (444568525133 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_15 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (522196988767 / 625000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (17365989121 / 781250000000 : ℝ))
      (E := (cell12941 ⟨15, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (522196988767 / 625000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (17365989121 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_16 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (2609905872123 / 3125000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111425299371 / 50000000000000 : ℝ))
      (E := (cell12941 ⟨16, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (2609905872123 / 3125000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111425299371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_17 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (8348248191551 / 10000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222854604269 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨17, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (8348248191551 / 10000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222854604269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_18 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (8344800019191 / 10000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (34732166073 / 1562500000000 : ℝ))
      (E := (cell12941 ⟨18, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (8344800019191 / 10000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (34732166073 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_19 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (4170677135189 / 5000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (222286261803 / 10000000000000 : ℝ))
      (E := (cell12941 ⟨19, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (4170677135189 / 5000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (222286261803 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12942_0 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (42036198840853 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (22226708749 / 1000000000000 : ℝ))
      (E := (cell12942 ⟨0, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (42036198840853 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (22226708749 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_1 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (84037499017627 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222674887313 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨1, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (84037499017627 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222674887313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_2 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (1312541018437 / 1562500000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555669718413 / 25000000000000 : ℝ))
      (E := (cell12942 ⟨2, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (1312541018437 / 1562500000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555669718413 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_3 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (16793555226493 / 20000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (88907316009 / 4000000000000 : ℝ))
      (E := (cell12942 ⟨3, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (16793555226493 / 20000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (88907316009 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_4 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (20983237959761 / 25000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555671729331 / 25000000000000 : ℝ))
      (E := (cell12942 ⟨4, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (20983237959761 / 25000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555671729331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_5 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (41949076131911 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222690874887 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨5, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (41949076131911 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222690874887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_6 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (16772675474221 / 20000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (222269489643 / 10000000000000 : ℝ))
      (E := (cell12942 ⟨6, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (16772675474221 / 20000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (222269489643 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_7 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (83828627125383 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (222269893141 / 10000000000000 : ℝ))
      (E := (cell12942 ⟨7, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (83828627125383 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (222269893141 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_8 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (41896950745667 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (444540585787 / 20000000000000 : ℝ))
      (E := (cell12942 ⟨8, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (41896950745667 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (444540585787 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_9 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (83759200433821 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (444541379163 / 20000000000000 : ℝ))
      (E := (cell12942 ⟨9, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (83759200433821 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (444541379163 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_10 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (83724523917887 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (55567772417 / 2500000000000 : ℝ))
      (E := (cell12942 ⟨10, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (83724523917887 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (55567772417 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_11 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (41844935954381 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222714937907 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨11, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (41844935954381 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222714937907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_12 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (20913811092963 / 25000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555679727351 / 25000000000000 : ℝ))
      (E := (cell12942 ⟨12, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (20913811092963 / 25000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555679727351 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_13 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (20905160318187 / 25000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (222272293319 / 10000000000000 : ℝ))
      (E := (cell12942 ⟨13, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (20905160318187 / 25000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (222272293319 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_14 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (41793031288607 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555681739187 / 25000000000000 : ℝ))
      (E := (cell12942 ⟨14, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (41793031288607 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555681739187 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_15 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (83551508251197 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (138920682951 / 6250000000000 : ℝ))
      (E := (cell12942 ⟨15, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (83551508251197 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (138920682951 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_16 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (5219811141301 / 6250000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222734966027 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨16, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (5219811141301 / 6250000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222734966027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_17 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (5217654535773 / 6250000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (1111369480813 / 50000000000000 : ℝ))
      (E := (cell12942 ⟨17, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (5217654535773 / 6250000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (1111369480813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_18 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (41723995576161 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2778428721 / 125000000000 : ℝ))
      (E := (cell12942 ⟨18, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (41723995576161 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2778428721 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_19 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (83413533967323 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222746957627 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨19, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (83413533967323 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222746957627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12943_0 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (84072383114779 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111277601619 / 50000000000000 : ℝ))
      (E := (cell12943 ⟨0, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (84072383114779 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111277601619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_1 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (1680749695231 / 2000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111279626097 / 50000000000000 : ℝ))
      (E := (cell12943 ⟨1, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (1680749695231 / 2000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111279626097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_2 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (42001305617151 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111281608977 / 50000000000000 : ℝ))
      (E := (cell12943 ⟨2, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (42001305617151 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111281608977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_3 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (83967762496771 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222567224663 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨3, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (83967762496771 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222567224663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_4 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (83932938512887 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222571222607 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨4, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (83932938512887 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222571222607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_5 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (41949069623383 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222575219677 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨5, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (41949069623383 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222575219677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_6 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (41931682331357 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222579223511 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨6, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (41931682331357 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222579223511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_7 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (10478576840653 / 12500000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (138911452593 / 6250000000000 : ℝ))
      (E := (cell12943 ⟨7, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (10478576840653 / 12500000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (138911452593 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_8 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (83793889398973 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111293640371 / 50000000000000 : ℝ))
      (E := (cell12943 ⟨8, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (83793889398973 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111293640371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_9 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (41879594324413 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (277823911263 / 12500000000000 : ℝ))
      (E := (cell12943 ⟨9, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (41879594324413 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (277823911263 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_10 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (20931128109957 / 25000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111297638067 / 50000000000000 : ℝ))
      (E := (cell12943 ⟨10, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (20931128109957 / 25000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111297638067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_11 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (83689860737207 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222599245143 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨11, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (83689860737207 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222599245143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_12 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (83655233506373 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222603261307 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨12, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (83655233506373 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222603261307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_13 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (16724126142583 / 20000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111303636187 / 50000000000000 : ℝ))
      (E := (cell12943 ⟨13, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (16724126142583 / 20000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111303636187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_14 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (83586052322601 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111305641957 / 50000000000000 : ℝ))
      (E := (cell12943 ⟨14, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (83586052322601 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111305641957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_15 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (83551498301377 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222615301251 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨15, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (83551498301377 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222615301251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_16 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (83516968615363 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222619271261 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨16, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (83516968615363 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222619271261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_17 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (10435307903857 / 12500000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111311657589 / 50000000000000 : ℝ))
      (E := (cell12943 ⟨17, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (10435307903857 / 12500000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111311657589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_18 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (83447982114329 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222627321159 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨18, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (83447982114329 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222627321159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_19 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (10426690654053 / 12500000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222631293493 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨19, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (10426690654053 / 12500000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222631293493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12944_0 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (16814473710021 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (277804948121 / 12500000000000 : ℝ))
      (E := (cell12944 ⟨0, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (16814473710021 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (277804948121 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_1 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (84037470507689 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222443612669 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨1, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (84037470507689 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222443612669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_2 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (16800519458163 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (222244761577 / 10000000000000 : ℝ))
      (E := (cell12944 ⟨2, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (16800519458163 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (222244761577 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_3 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (83967748863221 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (1111225801337 / 50000000000000 : ℝ))
      (E := (cell12944 ⟨3, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (83967748863221 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (1111225801337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_4 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (20983231297209 / 25000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222455639453 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨4, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (20983231297209 / 25000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222455639453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_5 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (41949063115889 / 50000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (1111229809083 / 50000000000000 : ℝ))
      (E := (cell12944 ⟨5, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (41949063115889 / 50000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (1111229809083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_6 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (16772670391271 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (44449272087 / 2000000000000 : ℝ))
      (E := (cell12944 ⟨6, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (16772670391271 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (44449272087 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_7 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (83828602327059 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (555616901347 / 25000000000000 : ℝ))
      (E := (cell12944 ⟨7, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (83828602327059 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (555616901347 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_8 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (83793877308571 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (277808953551 / 12500000000000 : ℝ))
      (E := (cell12944 ⟨8, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (83793877308571 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (277808953551 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_9 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (83759176865753 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (444495124449 / 20000000000000 : ℝ))
      (E := (cell12944 ⟨9, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (83759176865753 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (444495124449 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_10 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (83724500963653 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (88899186061 / 4000000000000 : ℝ))
      (E := (cell12944 ⟨10, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (83724500963653 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (88899186061 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_11 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (83689849567501 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (1111241832267 / 50000000000000 : ℝ))
      (E := (cell12944 ⟨11, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (83689849567501 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (1111241832267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_12 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (41827611321353 / 50000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (444497533467 / 20000000000000 : ℝ))
      (E := (cell12944 ⟨12, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (41827611321353 / 50000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (444497533467 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_13 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (83620620154859 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222491665741 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨13, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (83620620154859 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222491665741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_14 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (2612063814679 / 3125000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (555623916331 / 25000000000000 : ℝ))
      (E := (cell12944 ⟨14, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (2612063814679 / 3125000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (555623916331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_15 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (4177574417663 / 5000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222499671407 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨15, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (4177574417663 / 5000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222499671407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_16 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (10439619871447 / 12500000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (138906480567 / 6250000000000 : ℝ))
      (E := (cell12944 ⟨16, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (10439619871447 / 12500000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (138906480567 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_17 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (2608826684093 / 3125000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (88900306597 / 4000000000000 : ℝ))
      (E := (cell12944 ⟨17, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (2608826684093 / 3125000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (88900306597 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_18 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (8344797307793 / 10000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222511661751 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨18, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (8344797307793 / 10000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222511661751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_19 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (20853379124771 / 25000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222515683907 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨19, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (20853379124771 / 25000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222515683907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12945_0 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (16814470797537 / 20000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222324020089 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨0, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (16814470797537 / 20000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222324020089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_1 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (21009364064011 / 25000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222328026599 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨1, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (21009364064011 / 25000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222328026599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_2 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (84002583349507 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222332009221 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨2, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (84002583349507 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222332009221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_3 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (20991933807953 / 25000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111168017131 / 50000000000000 : ℝ))
      (E := (cell12945 ⟨3, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (20991933807953 / 25000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111168017131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_4 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (83932911866889 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111169997041 / 50000000000000 : ℝ))
      (E := (cell12945 ⟨4, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (83932911866889 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111169997041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_5 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (83898113218859 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (5555860031 / 250000000000 : ℝ))
      (E := (cell12945 ⟨5, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (83898113218859 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (5555860031 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_6 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (83863339252027 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (555587009737 / 25000000000000 : ℝ))
      (E := (cell12945 ⟨6, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (83863339252027 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (555587009737 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_7 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (8382858993089 / 10000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111176011553 / 50000000000000 : ℝ))
      (E := (cell12945 ⟨7, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (8382858993089 / 10000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111176011553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_8 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (41896932610063 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (555589007489 / 25000000000000 : ℝ))
      (E := (cell12945 ⟨8, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (41896932610063 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (555589007489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_9 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (83759165084601 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222360066373 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨9, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (83759165084601 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222360066373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_10 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (20931122372341 / 25000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222364022849 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨10, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (20931122372341 / 25000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222364022849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_11 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (83689838399643 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (444473604361 / 20000000000000 : ℝ))
      (E := (cell12945 ⟨11, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (83689838399643 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (444473604361 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_12 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (83655211780851 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (555593017343 / 25000000000000 : ℝ))
      (E := (cell12945 ⟨12, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (83655211780851 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (555593017343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_13 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (41810304799289 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (555594013789 / 25000000000000 : ℝ))
      (E := (cell12945 ⟨13, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (41810304799289 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (555594013789 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_14 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (83586031818593 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (111119002141 / 5000000000000 : ℝ))
      (E := (cell12945 ⟨14, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (83586031818593 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (111119002141 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_15 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (16710295681369 / 20000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (222238409587 / 10000000000000 : ℝ))
      (E := (cell12945 ⟨15, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (16710295681369 / 20000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (222238409587 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_16 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (5219809333091 / 6250000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (69449626401 / 3125000000000 : ℝ))
      (E := (cell12945 ⟨16, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (5219809333091 / 6250000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (69449626401 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_17 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (3339297782109 / 4000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (22223920691 / 1000000000000 : ℝ))
      (E := (cell12945 ⟨17, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (3339297782109 / 4000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (22223920691 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_18 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (133516742469 / 160000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222396056831 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨18, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (133516742469 / 160000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222396056831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_19 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (41706753883651 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (222240007059 / 10000000000000 : ℝ))
      (E := (cell12945 ⟨19, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (41706753883651 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (222240007059 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12946_0 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (84072339427517 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (222220845077 / 10000000000000 : ℝ))
      (E := (cell12946 ⟨0, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (84072339427517 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (222220845077 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_1 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (16807488401323 / 20000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (555553109031 / 25000000000000 : ℝ))
      (E := (cell12946 ⟨1, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (16807488401323 / 20000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (555553109031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_2 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (84002569410377 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222216456187 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨2, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (84002569410377 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222216456187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_3 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (5247982600159 / 6250000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (555555115381 / 25000000000000 : ℝ))
      (E := (cell12946 ⟨3, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (5247982600159 / 6250000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (555555115381 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_4 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (10491612318381 / 12500000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222224460277 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨4, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (10491612318381 / 12500000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222224460277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_5 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (83898100208007 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (138889278771 / 6250000000000 : ℝ))
      (E := (cell12946 ⟨5, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (83898100208007 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (138889278771 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_6 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (8386332654973 / 10000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222232469333 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨6, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (8386332654973 / 10000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222232469333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_7 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (41914288768357 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (44444728733 / 2000000000000 : ℝ))
      (E := (cell12946 ⟨7, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (41914288768357 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (44444728733 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_8 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (83793853133639 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222240485387 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨8, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (83793853133639 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222240485387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_9 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (83759153305371 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (444448889671 / 20000000000000 : ℝ))
      (E := (cell12946 ⟨9, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (83759153305371 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (444448889671 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_10 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (41862239008479 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222248448179 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨10, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (41862239008479 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222248448179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_11 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (83689827233633 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (1111126245617 / 50000000000000 : ℝ))
      (E := (cell12946 ⟨11, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (83689827233633 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (1111126245617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_12 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (83655200920807 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222256467421 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨12, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (83655200920807 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222256467421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_13 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (83620599044071 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222260498759 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨13, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (83620599044071 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222260498759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_14 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (83586021569197 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222264474563 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨14, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (83586021569197 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222264474563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_15 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (83551468462133 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (444453703291 / 20000000000000 : ℝ))
      (E := (cell12946 ⟨15, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (83551468462133 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (444453703291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_16 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (41758469844501 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222272513169 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨16, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (41758469844501 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222272513169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_17 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (10435304402013 / 12500000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (444455305541 / 20000000000000 : ℝ))
      (E := (cell12946 ⟨17, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (10435304402013 / 12500000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (444455305541 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_18 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (41723977504957 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222280506401 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨18, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (41723977504957 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222280506401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_19 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (83413499037077 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (138892781989 / 6250000000000 : ℝ))
      (E := (cell12946 ⟨19, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (83413499037077 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (138892781989 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12947_0 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (84072324869601 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (555523219253 / 25000000000000 : ℝ))
      (E := (cell12947 ⟨0, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (84072324869601 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (555523219253 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_1 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (420187138797 / 500000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (555524224777 / 25000000000000 : ℝ))
      (E := (cell12947 ⟨1, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (420187138797 / 500000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (555524224777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_2 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (42001277736713 / 50000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (222210089879 / 10000000000000 : ℝ))
      (E := (cell12947 ⟨2, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (42001277736713 / 50000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (222210089879 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_3 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (41983853987709 / 50000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (111105244223 / 5000000000000 : ℝ))
      (E := (cell12947 ⟨3, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (41983853987709 / 50000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (111105244223 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_4 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (8393288522931 / 10000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (444421784437 / 20000000000000 : ℝ))
      (E := (cell12947 ⟨4, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (8393288522931 / 10000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (444421784437 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_5 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (41949043599611 / 50000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111056452011 / 50000000000000 : ℝ))
      (E := (cell12947 ⟨5, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (41949043599611 / 50000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111056452011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_6 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (10482914231183 / 12500000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111058447753 / 50000000000000 : ℝ))
      (E := (cell12947 ⟨6, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (10482914231183 / 12500000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111058447753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_7 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (20957141286133 / 25000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222120904017 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨7, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (20957141286133 / 25000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222120904017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_8 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (83793841049109 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222124936681 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨8, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (83793841049109 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222124936681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_9 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (4187957076403 / 5000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222128942329 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨9, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (4187957076403 / 5000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222128942329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_10 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (83724466546437 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (444426585503 / 20000000000000 : ℝ))
      (E := (cell12947 ⟨10, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (83724466546437 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (444426585503 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_11 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (8368981606947 / 10000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111068478319 / 50000000000000 : ℝ))
      (E := (cell12947 ⟨11, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (8368981606947 / 10000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111068478319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_12 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (83655190062573 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111070459799 / 50000000000000 : ℝ))
      (E := (cell12947 ⟨12, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (83655190062573 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111070459799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_13 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (83620588491339 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (555536234603 / 25000000000000 : ℝ))
      (E := (cell12947 ⟨13, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (83620588491339 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (555536234603 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_14 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (83586011321539 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (555537240139 / 25000000000000 : ℝ))
      (E := (cell12947 ⟨14, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (83586011321539 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (555537240139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_15 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (41775729259561 / 50000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111076466583 / 50000000000000 : ℝ))
      (E := (cell12947 ⟨15, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (41775729259561 / 50000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111076466583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_16 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (83516930050213 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222156977669 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨16, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (83516930050213 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222156977669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_17 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (83482425881113 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (555540245627 / 25000000000000 : ℝ))
      (E := (cell12947 ⟨17, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (83482425881113 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (555540245627 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_18 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (10430993247287 / 12500000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222164952207 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨18, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (10430993247287 / 12500000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222164952207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_19 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (83413490308409 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222168949331 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨19, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (83413490308409 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222168949331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12948_0 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (84072310313937 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2221977356649 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨0, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (84072310313937 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2221977356649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_1 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (84037413514401 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (222198135769 / 10000000000000 : ℝ))
      (E := (cell12948 ⟨1, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (84037413514401 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (222198135769 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_2 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (21000635384663 / 25000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (69437043591 / 3125000000000 : ℝ))
      (E := (cell12948 ⟨2, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (21000635384663 / 25000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (69437043591 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_3 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (2623990448451 / 3125000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (88879574439 / 4000000000000 : ℝ))
      (E := (cell12948 ⟨3, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (2623990448451 / 3125000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (88879574439 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_4 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (20983217978419 / 25000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1110996689903 / 50000000000000 : ℝ))
      (E := (cell12948 ⟨4, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (20983217978419 / 25000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1110996689903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_5 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (10487259274063 / 12500000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (222199740141 / 10000000000000 : ℝ))
      (E := (cell12948 ⟨5, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (10487259274063 / 12500000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (222199740141 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_6 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (20965825287807 / 25000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1111000687721 / 50000000000000 : ℝ))
      (E := (cell12948 ⟨6, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (20965825287807 / 25000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1111000687721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_7 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (10478569094293 / 12500000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (222200536721 / 10000000000000 : ℝ))
      (E := (cell12948 ⟨7, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (10478569094293 / 12500000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (222200536721 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_8 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (16758765793307 / 20000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222009383839 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨8, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (16758765793307 / 20000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222009383839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_9 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (8375912975267 / 10000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1111006687079 / 50000000000000 : ℝ))
      (E := (cell12948 ⟨9, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (8375912975267 / 10000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1111006687079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_10 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (41862227538899 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (222201740279 / 10000000000000 : ℝ))
      (E := (cell12948 ⟨10, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (41862227538899 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (222201740279 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_11 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (41844902453577 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222021418019 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨11, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (41844902453577 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222021418019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_12 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (1673103584123 / 2000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (138876589119 / 6250000000000 : ℝ))
      (E := (cell12948 ⟨12, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (1673103584123 / 2000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (138876589119 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_13 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (83620577940381 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1111014716127 / 50000000000000 : ℝ))
      (E := (cell12948 ⟨13, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (83620577940381 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1111014716127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_14 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (83586001075619 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (555508360659 / 25000000000000 : ℝ))
      (E := (cell12948 ⟨14, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (83586001075619 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (555508360659 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_15 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (83551448577813 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222037404187 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨15, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (83551448577813 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222037404187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_16 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (8351692041309 / 10000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222041438331 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨16, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (8351692041309 / 10000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222041438331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_17 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (333929666191 / 400000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222045433511 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨17, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (333929666191 / 400000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222045433511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_18 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (8344793694827 / 10000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (444409890501 / 20000000000000 : ℝ))
      (E := (cell12948 ⟨18, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (8344793694827 / 10000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (444409890501 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_19 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (83413481581297 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222053441391 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨19, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (83413481581297 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222053441391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12949_0 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (21018073940131 / 25000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1110930944841 / 50000000000000 : ℝ))
      (E := (cell12949 ⟨0, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (21018073940131 / 25000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1110930944841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_1 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (16807479854323 / 20000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221865869729 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨1, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (16807479854323 / 20000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221865869729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_2 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (42001263803027 / 50000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (138866867917 / 6250000000000 : ℝ))
      (E := (cell12949 ⟨2, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (42001263803027 / 50000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (138866867917 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_3 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (83967680727587 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (222187389107 / 10000000000000 : ℝ))
      (E := (cell12949 ⟨3, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (83967680727587 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (222187389107 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_4 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (16786571720029 / 20000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555469472767 / 25000000000000 : ℝ))
      (E := (cell12949 ⟨4, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (16786571720029 / 20000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555469472767 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_5 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (20974515296963 / 25000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555470473637 / 25000000000000 : ℝ))
      (E := (cell12949 ⟨5, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (20974515296963 / 25000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555470473637 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_6 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (83863288455021 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221885909141 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨6, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (83863288455021 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221885909141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_7 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (20957135091537 / 25000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221889884227 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨7, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (20957135091537 / 25000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221889884227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_8 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (41896908442959 / 50000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221893884881 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨8, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (41896908442959 / 50000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221893884881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_9 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (83759117979199 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1110948958989 / 50000000000000 : ℝ))
      (E := (cell12949 ⟨9, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (83759117979199 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1110948958989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_10 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (83724443611043 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221901874003 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨10, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (83724443611043 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221901874003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_11 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (20922448436671 / 25000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555476483367 / 25000000000000 : ℝ))
      (E := (cell12949 ⟨11, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (20922448436671 / 25000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555476483367 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_12 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (83655168351537 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221909928223 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨12, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (83655168351537 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221909928223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_13 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (83620567391197 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1110956961073 / 50000000000000 : ℝ))
      (E := (cell12949 ⟨13, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (83620567391197 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1110956961073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_14 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (16717198166287 / 20000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (444383584161 / 20000000000000 : ℝ))
      (E := (cell12949 ⟨14, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (16717198166287 / 20000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (444383584161 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_15 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (20887859659551 / 25000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221921929519 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨15, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (20887859659551 / 25000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221921929519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_16 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (8351691077763 / 10000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555481488341 / 25000000000000 : ℝ))
      (E := (cell12949 ⟨16, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (8351691077763 / 10000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555481488341 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_17 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (5217650451001 / 6250000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (135615841 / 6103515625 : ℝ))
      (E := (cell12949 ⟨17, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (5217650451001 / 6250000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (135615841 / 6103515625 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_18 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (83447927919837 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221933949039 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨18, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (83447927919837 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221933949039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_19 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (41706736427871 / 50000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221937929723 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨19, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (41706736427871 / 50000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221937929723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

end BstLean.Part268
