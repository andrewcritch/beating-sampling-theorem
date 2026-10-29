import BstLean.Part268CellShard23Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12925_20 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (41689622282641 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224720787741 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨20, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (41689622282641 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224720787741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_21 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (8334483060721 / 10000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224724839743 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨21, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (8334483060721 / 10000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224724839743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_22 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (833104407923 / 1000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (556182199663 / 25000000000000 : ℝ))
      (E := (cell12925 ⟨22, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (833104407923 / 1000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (556182199663 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_23 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (83276075087863 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (111236642143 / 5000000000000 : ℝ))
      (E := (cell12925 ⟨23, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (83276075087863 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (111236642143 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_24 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (665933867691 / 800000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224736858839 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨24, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (665933867691 / 800000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224736858839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_25 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (41603707940241 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (222474084947 / 10000000000000 : ℝ))
      (E := (cell12925 ⟨25, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (41603707940241 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (222474084947 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_26 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (41586561156497 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (444948963481 / 20000000000000 : ℝ))
      (E := (cell12925 ⟨26, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (41586561156497 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (444948963481 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_27 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (83138852726887 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (556187205881 / 25000000000000 : ℝ))
      (E := (cell12925 ⟨27, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (83138852726887 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (556187205881 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_28 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (41552303545149 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (444950574017 / 20000000000000 : ℝ))
      (E := (cell12925 ⟨28, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (41552303545149 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (444950574017 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_29 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (10383798171441 / 12500000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224756842093 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨29, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (10383798171441 / 12500000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224756842093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_30 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (41518093769521 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224760858271 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨30, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (41518093769521 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224760858271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_31 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (41501006780731 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224764861631 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨31, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (41501006780731 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224764861631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_32 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (82967863407571 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (1112384456013 / 50000000000000 : ℝ))
      (E := (cell12925 ⟨32, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (82967863407571 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (1112384456013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_33 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (10366717130789 / 12500000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (27809661167 / 1250000000000 : ℝ))
      (E := (cell12925 ⟨33, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (10366717130789 / 12500000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (27809661167 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_34 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (82899634446783 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224776923639 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨34, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (82899634446783 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224776923639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_35 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (41432777789121 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (1112390443111 / 50000000000000 : ℝ))
      (E := (cell12925 ⟨35, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (41432777789121 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (1112390443111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_36 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (828315004101 / 1000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (55619622469 / 2500000000000 : ℝ))
      (E := (cell12925 ⟨36, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (828315004101 / 1000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (55619622469 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_37 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (20699367227981 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (556197225693 / 25000000000000 : ℝ))
      (E := (cell12925 ⟨37, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (20699367227981 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (556197225693 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_38 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (16552692210687 / 20000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224792898183 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨38, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (16552692210687 / 20000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224792898183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_39 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (20682369201127 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (27809961793 / 1250000000000 : ℝ))
      (E := (cell12925 ⟨39, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (20682369201127 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (27809961793 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12926_20 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (83379236107121 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112302356169 / 50000000000000 : ℝ))
      (E := (cell12926 ⟨20, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (83379236107121 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112302356169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_21 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (41672411225957 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (88984350257 / 4000000000000 : ℝ))
      (E := (cell12926 ⟨21, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (41672411225957 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (88984350257 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_22 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (41655216469723 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224612766463 / 100000000000000 : ℝ))
      (E := (cell12926 ⟨22, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (41655216469723 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224612766463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_23 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (83276067537031 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112308372901 / 50000000000000 : ℝ))
      (E := (cell12926 ⟨23, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (83276067537031 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112308372901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_24 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (16648345242429 / 20000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (444924151191 / 20000000000000 : ℝ))
      (E := (cell12926 ⟨24, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (16648345242429 / 20000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (444924151191 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_25 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (16641481786487 / 20000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112312370727 / 50000000000000 : ℝ))
      (E := (cell12926 ⟨25, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (16641481786487 / 20000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112312370727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_26 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (5198319729107 / 6250000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224628763391 / 100000000000000 : ℝ))
      (E := (cell12926 ⟨26, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (5198319729107 / 6250000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224628763391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_27 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (5196177898747 / 6250000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (556158191447 / 25000000000000 : ℝ))
      (E := (cell12926 ⟨27, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (5196177898747 / 6250000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (556158191447 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_28 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (83104601043293 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (55615920233 / 2500000000000 : ℝ))
      (E := (cell12926 ⟨28, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (83104601043293 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (55615920233 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_29 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (83070379624039 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (556160194747 / 25000000000000 : ℝ))
      (E := (cell12926 ⟨29, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (83070379624039 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (556160194747 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_30 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (83036182090653 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112322396759 / 50000000000000 : ℝ))
      (E := (cell12926 ⟨30, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (83036182090653 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112322396759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_31 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (41501004205879 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224648795921 / 100000000000000 : ℝ))
      (E := (cell12926 ⟨31, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (41501004205879 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224648795921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_32 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (4148392927807 / 5000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (444930557493 / 20000000000000 : ℝ))
      (E := (cell12926 ⟨32, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (4148392927807 / 5000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (444930557493 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_33 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (82933732492741 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224656827799 / 100000000000000 : ℝ))
      (E := (cell12926 ⟨33, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (82933732492741 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224656827799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_34 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (4144981509533 / 5000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (556165200139 / 25000000000000 : ℝ))
      (E := (cell12926 ⟨34, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (4144981509533 / 5000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (556165200139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_35 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (20716387904789 / 25000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (55616620589 / 2500000000000 : ℝ))
      (E := (cell12926 ⟨35, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (20716387904789 / 25000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (55616620589 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_36 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (82831496747641 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224668838577 / 100000000000000 : ℝ))
      (E := (cell12926 ⟨36, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (82831496747641 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224668838577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_37 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (82797465545683 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (278084105719 / 12500000000000 : ℝ))
      (E := (cell12926 ⟨37, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (82797465545683 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (278084105719 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_38 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (82763457983003 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224676845011 / 100000000000000 : ℝ))
      (E := (cell12926 ⟨38, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (82763457983003 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224676845011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_39 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (20682368507369 / 25000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224680836057 / 100000000000000 : ℝ))
      (E := (cell12926 ⟨39, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (20682368507369 / 25000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224680836057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12927_20 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (83379227650489 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (88979547661 / 4000000000000 : ℝ))
      (E := (cell12927 ⟨20, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (83379227650489 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (88979547661 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_21 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (8334481429811 / 10000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112246334717 / 50000000000000 : ℝ))
      (E := (cell12927 ⟨21, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (8334481429811 / 10000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112246334717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_22 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (83310425088049 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224496672291 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨22, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (83310425088049 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224496672291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_23 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (83276059987619 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224500703517 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨23, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (83276059987619 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224500703517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_24 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (83241718964299 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224504707903 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨24, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (83241718964299 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224504707903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_25 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (10400925248217 / 12500000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224508688331 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨25, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (10400925248217 / 12500000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224508688331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_26 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (41586554509871 / 50000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (222451270589 / 10000000000000 : ℝ))
      (E := (cell12927 ⟨26, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (41586554509871 / 50000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (222451270589 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_27 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (83138840034293 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112258352301 / 50000000000000 : ℝ))
      (E := (cell12927 ⟨27, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (83138840034293 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112258352301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_28 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (8310459499753 / 10000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224520745139 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨28, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (8310459499753 / 10000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224520745139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_29 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (16614074775551 / 20000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (444904942501 / 20000000000000 : ℝ))
      (E := (cell12927 ⟨29, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (16614074775551 / 20000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (444904942501 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_30 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (83036176643433 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (139033045339 / 6250000000000 : ℝ))
      (E := (cell12927 ⟨30, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (83036176643433 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (139033045339 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_31 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (83002003263189 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (278066590863 / 12500000000000 : ℝ))
      (E := (cell12927 ⟨31, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (83002003263189 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (278066590863 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_32 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (5185490856613 / 6250000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (556134194199 / 25000000000000 : ℝ))
      (E := (cell12927 ⟨32, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (5185490856613 / 6250000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (556134194199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_33 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (82933727940233 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (556135189751 / 25000000000000 : ℝ))
      (E := (cell12927 ⟨33, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (82933727940233 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (556135189751 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_34 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (16579925187113 / 20000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (556136197883 / 25000000000000 : ℝ))
      (E := (cell12927 ⟨34, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (16579925187113 / 20000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (556136197883 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_35 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (82865547661063 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224548757737 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨35, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (82865547661063 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224548757737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_36 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (82831493086139 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224552775269 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨36, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (82831493086139 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224552775269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_37 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (82797462180363 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (444911357129 / 20000000000000 : ℝ))
      (E := (cell12927 ⟨37, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (82797462180363 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (444911357129 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_38 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (82763454913457 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224560788789 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨38, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (82763454913457 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224560788789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_39 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (323161997091 / 390625000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112282392201 / 50000000000000 : ℝ))
      (E := (cell12927 ⟨39, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (323161997091 / 390625000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112282392201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12928_20 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (41689609597693 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112186333501 / 50000000000000 : ℝ))
      (E := (cell12928 ⟨20, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (41689609597693 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112186333501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_21 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (41672403072899 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224376695419 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨21, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (41672403072899 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224376695419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_22 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (20827604309527 / 25000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224380691179 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨22, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (20827604309527 / 25000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224380691179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_23 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (83276052439627 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224384657633 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨23, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (83276052439627 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224384657633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_24 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (41620855858919 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224388656289 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨24, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (41620855858919 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224388656289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_25 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (41603697520193 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (22243926901 / 1000000000000 : ℝ))
      (E := (cell12928 ⟨25, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (41603697520193 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (22243926901 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_26 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (16634620475017 / 20000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (111219835167 / 5000000000000 : ℝ))
      (E := (cell12928 ⟨26, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (16634620475017 / 20000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (111219835167 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_27 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (83138833689911 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556100174607 / 25000000000000 : ℝ))
      (E := (cell12928 ⟨27, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (83138833689911 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556100174607 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_28 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (83104588953007 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (69512648001 / 3125000000000 : ℝ))
      (E := (cell12928 ⟨28, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (83104588953007 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (69512648001 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_29 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (20767592033169 / 25000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556102175289 / 25000000000000 : ℝ))
      (E := (cell12928 ⟨29, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (20767592033169 / 25000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556102175289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_30 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (83036171197383 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112206356261 / 50000000000000 : ℝ))
      (E := (cell12928 ⟨30, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (83036171197383 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112206356261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_31 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (41500999057877 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (111220835657 / 5000000000000 : ℝ))
      (E := (cell12928 ⟨31, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (41500999057877 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (111220835657 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_32 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (41483924428287 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112210352139 / 50000000000000 : ℝ))
      (E := (cell12928 ⟨32, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (41483924428287 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112210352139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_33 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (20733430847197 / 25000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112212372791 / 50000000000000 : ℝ))
      (E := (cell12928 ⟨33, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (20733430847197 / 25000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112212372791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_34 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (82899621681497 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556107180171 / 25000000000000 : ℝ))
      (E := (cell12928 ⟨34, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (82899621681497 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556107180171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_35 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (82865543703961 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112216373703 / 50000000000000 : ℝ))
      (E := (cell12928 ⟨35, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (82865543703961 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112216373703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_36 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (41415744712797 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224436767513 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨36, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (41415744712797 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224436767513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_37 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (16559491763193 / 20000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556110195287 / 25000000000000 : ℝ))
      (E := (cell12928 ⟨37, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (16559491763193 / 20000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556110195287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_38 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (82763451844797 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556111197059 / 25000000000000 : ℝ))
      (E := (cell12928 ⟨38, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (82763451844797 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556111197059 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_39 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (41364734240983 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112224394239 / 50000000000000 : ℝ))
      (E := (cell12928 ⟨39, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (41364734240983 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112224394239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12929_20 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (8337921074181 / 10000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224256638773 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨20, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (8337921074181 / 10000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224256638773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_21 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (41672398997489 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224260659409 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨21, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (41672398997489 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224260659409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_22 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (41655204694811 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112132324043 / 50000000000000 : ℝ))
      (E := (cell12929 ⟨22, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (41655204694811 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112132324043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_23 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (16655208978611 / 20000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224268666523 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨23, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (16655208978611 / 20000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224268666523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_24 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (2081042611819 / 2500000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (222427265951 / 10000000000000 : ℝ))
      (E := (cell12929 ⟨24, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (2081042611819 / 2500000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (222427265951 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_25 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (83207388096383 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112138344173 / 50000000000000 : ℝ))
      (E := (cell12929 ⟨25, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (83207388096383 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112138344173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_26 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (83173095731739 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (444856139461 / 20000000000000 : ℝ))
      (E := (cell12929 ⟨26, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (83173095731739 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (444856139461 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_27 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (41569413673403 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224284688803 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨27, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (41569413673403 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224284688803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_28 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (3324183316389 / 4000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224288723511 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨28, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (3324183316389 / 4000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224288723511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_29 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (41535181194401 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224292686429 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨29, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (41535181194401 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224292686429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_30 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (41518082876251 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224296696281 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨30, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (41518082876251 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224296696281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_31 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (20750498242363 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224300754631 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨31, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (20750498242363 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224300754631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_32 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (41483922004219 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (444860949131 / 20000000000000 : ℝ))
      (E := (cell12929 ⟨32, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (41483922004219 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (444860949131 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_33 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (16586743767681 / 20000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (222430872893 / 10000000000000 : ℝ))
      (E := (cell12929 ⟨33, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (16586743767681 / 20000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (222430872893 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_34 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (82899617428457 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224312763897 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨34, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (82899617428457 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224312763897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_35 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (20716384936963 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556079183479 / 25000000000000 : ℝ))
      (E := (cell12929 ⟨35, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (20716384936963 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556079183479 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_36 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (16566297153201 / 20000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112160378317 / 50000000000000 : ℝ))
      (E := (cell12929 ⟨36, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (16566297153201 / 20000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112160378317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_37 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (10349681931561 / 12500000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112162386783 / 50000000000000 : ℝ))
      (E := (cell12929 ⟨37, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (10349681931561 / 12500000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112162386783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_38 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (82763448777023 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112164392317 / 50000000000000 : ℝ))
      (E := (cell12929 ⟨38, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (82763448777023 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112164392317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_39 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (5170591606843 / 6250000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224332789539 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨39, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (5170591606843 / 6250000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224332789539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12930_20 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (41689601144881 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (139008791571 / 6250000000000 : ℝ))
      (E := (cell12930 ⟨20, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (41689601144881 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (139008791571 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_21 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (83344789845649 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224144678053 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨21, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (83344789845649 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224144678053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_22 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (83310401542591 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112074359027 / 50000000000000 : ℝ))
      (E := (cell12930 ⟨22, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (83310401542591 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112074359027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_23 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (83276037347903 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224152730187 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨23, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (83276037347903 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224152730187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_24 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (16648339445813 / 20000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112078358783 / 50000000000000 : ℝ))
      (E := (cell12930 ⟨24, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (16648339445813 / 20000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112078358783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_25 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (1300115330527 / 1562500000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224160741487 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨25, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (1300115330527 / 1562500000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224160741487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_26 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (16634617817941 / 20000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (88966589849 / 4000000000000 : ℝ))
      (E := (cell12930 ⟨26, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (16634617817941 / 20000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (88966589849 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_27 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (5196176312811 / 6250000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112084367097 / 50000000000000 : ℝ))
      (E := (cell12930 ⟨27, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (5196176312811 / 6250000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112084367097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_28 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (83104576867683 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112086353789 / 50000000000000 : ℝ))
      (E := (cell12930 ⟨28, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (83104576867683 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112086353789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_29 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (20767589161533 / 25000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112088363419 / 50000000000000 : ℝ))
      (E := (cell12930 ⟨29, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (20767589161533 / 25000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112088363419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_30 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (83036160308789 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112090367617 / 50000000000000 : ℝ))
      (E := (cell12930 ⟨30, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (83036160308789 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112090367617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_31 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (83001987824283 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (111209236713 / 5000000000000 : ℝ))
      (E := (cell12930 ⟨31, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (83001987824283 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (111209236713 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_32 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (82967839161399 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112094391883 / 50000000000000 : ℝ))
      (E := (cell12930 ⟨32, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (82967839161399 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112094391883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_33 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (16586742857817 / 20000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (44483855353 / 2000000000000 : ℝ))
      (E := (cell12930 ⟨33, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (16586742857817 / 20000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (44483855353 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_34 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (82899613176443 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (278024593161 / 12500000000000 : ℝ))
      (E := (cell12930 ⟨34, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (82899613176443 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (278024593161 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_35 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (41432767896367 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (27802509699 / 1250000000000 : ℝ))
      (E := (cell12930 ⟨35, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (41432767896367 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (27802509699 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_36 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (82831482107373 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (556051200327 / 25000000000000 : ℝ))
      (E := (cell12930 ⟨36, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (82831482107373 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (556051200327 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_37 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (82797452089931 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (556052205399 / 25000000000000 : ℝ))
      (E := (cell12930 ⟨37, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (82797452089931 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (556052205399 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_38 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (41381722855067 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112106388991 / 50000000000000 : ℝ))
      (E := (cell12930 ⟨38, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (41381722855067 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112106388991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_39 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (82729462937859 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (556054196897 / 25000000000000 : ℝ))
      (E := (cell12930 ⟨39, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (82729462937859 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (556054196897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12931_20 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (83379193839241 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (139001546631 / 6250000000000 : ℝ))
      (E := (cell12931 ⟨20, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (83379193839241 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (139001546631 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_21 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (83344781697811 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1112014375677 / 50000000000000 : ℝ))
      (E := (cell12931 ⟨21, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (83344781697811 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1112014375677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_22 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (10413799212127 / 12500000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (556008181511 / 25000000000000 : ℝ))
      (E := (cell12931 ⟨22, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (10413799212127 / 12500000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (556008181511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_23 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (83276029804169 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224036731887 / 100000000000000 : ℝ))
      (E := (cell12931 ⟨23, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (83276029804169 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224036731887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_24 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (41620844993377 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (69501274127 / 3125000000000 : ℝ))
      (E := (cell12931 ⟨24, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (41620844993377 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (69501274127 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_25 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (4160368710621 / 5000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224044791107 / 100000000000000 : ℝ))
      (E := (cell12931 ⟨25, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (4160368710621 / 5000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224044791107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_26 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (83173082448983 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224048791661 / 100000000000000 : ℝ))
      (E := (cell12931 ⟨26, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (83173082448983 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224048791661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_27 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (41569407332211 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1112026388069 / 50000000000000 : ℝ))
      (E := (cell12931 ⟨27, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (41569407332211 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1112026388069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_28 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (83104570826881 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224056805209 / 100000000000000 : ℝ))
      (E := (cell12931 ⟨28, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (83104570826881 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224056805209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_29 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (41535175452333 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224060763873 / 100000000000000 : ℝ))
      (E := (cell12931 ⟨29, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (41535175452333 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224060763873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_30 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (41518077433123 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224064770849 / 100000000000000 : ℝ))
      (E := (cell12931 ⟨30, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (41518077433123 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224064770849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_31 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (83001982680247 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (444813765541 / 20000000000000 : ℝ))
      (E := (cell12931 ⟨31, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (83001982680247 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (444813765541 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_32 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (82967834315459 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224072818611 / 100000000000000 : ℝ))
      (E := (cell12931 ⟨32, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (82967834315459 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224072818611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_33 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (82933709740827 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224076803143 / 100000000000000 : ℝ))
      (E := (cell12931 ⟨33, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (82933709740827 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224076803143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_34 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (5181225557841 / 6250000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224080840743 / 100000000000000 : ℝ))
      (E := (cell12931 ⟨34, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (5181225557841 / 6250000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224080840743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_35 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (82865531838607 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (139005300923 / 6250000000000 : ℝ))
      (E := (cell12931 ⟨35, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (82865531838607 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (139005300923 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_36 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (2588483701553 / 3125000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224088842863 / 100000000000000 : ℝ))
      (E := (cell12931 ⟨36, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (2588483701553 / 3125000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224088842863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_37 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (10349681091037 / 12500000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1112046433271 / 50000000000000 : ℝ))
      (E := (cell12931 ⟨37, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (10349681091037 / 12500000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1112046433271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_38 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (20690860661033 / 25000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (556024206751 / 25000000000000 : ℝ))
      (E := (cell12931 ⟨38, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (20690860661033 / 25000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (556024206751 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_39 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (41364730083541 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (278012605171 / 12500000000000 : ℝ))
      (E := (cell12931 ⟨39, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (41364730083541 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (278012605171 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12932_20 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (41689592695123 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (44478176467 / 2000000000000 : ℝ))
      (E := (cell12932 ⟨20, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (41689592695123 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (44478176467 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_21 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (10418096693933 / 12500000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (444782564197 / 20000000000000 : ℝ))
      (E := (cell12932 ⟨21, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (10418096693933 / 12500000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (444782564197 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_22 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (16662077170579 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223916847097 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨22, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (16662077170579 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223916847097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_23 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (41638011130927 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223920846733 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨23, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (41638011130927 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223920846733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_24 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (3329667309833 / 4000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (555981205751 / 25000000000000 : ℝ))
      (E := (cell12932 ⟨24, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (3329667309833 / 4000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (555981205751 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_25 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (41603683636229 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223928837207 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨25, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (41603683636229 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223928837207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_26 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (83173075809571 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (555983208403 / 25000000000000 : ℝ))
      (E := (cell12932 ⟨26, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (83173075809571 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (555983208403 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_27 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (83138808325143 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111968436549 / 50000000000000 : ℝ))
      (E := (cell12932 ⟨27, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (83138808325143 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111968436549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_28 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (41552282393659 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111970420471 / 50000000000000 : ℝ))
      (E := (cell12932 ⟨28, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (41552282393659 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111970420471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_29 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (16614069032881 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223944856043 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨29, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (16614069032881 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223944856043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_30 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (8303614942487 / 10000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223948861661 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨30, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (8303614942487 / 10000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223948861661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_31 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (1296905899021 / 1562500000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223952859289 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨31, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (1296905899021 / 1562500000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223952859289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_32 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (16593565894123 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (555989227193 / 25000000000000 : ℝ))
      (E := (cell12932 ⟨32, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (16593565894123 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (555989227193 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_33 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (8293370519363 / 10000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223960894011 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨33, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (8293370519363 / 10000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223960894011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_34 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (16579920935099 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223964874377 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨34, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (16579920935099 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223964874377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_35 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (82865527885471 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223968909111 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨35, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (82865527885471 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223968909111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_36 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (3313258991719 / 4000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (555993234993 / 25000000000000 : ℝ))
      (E := (cell12932 ⟨36, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (3313258991719 / 4000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (555993234993 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_37 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (82797445367581 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223976908403 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨37, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (82797445367581 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223976908403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_38 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (41381719789507 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223980931699 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨38, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (41381719789507 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223980931699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_39 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (41364728698577 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223984950883 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨39, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (41364728698577 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2223984950883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12933_20 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (41689588471389 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (22237928969 / 1000000000000 : ℝ))
      (E := (cell12933 ⟨20, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (41689588471389 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (22237928969 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_21 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (83344765406607 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111898472637 / 50000000000000 : ℝ))
      (E := (cell12933 ⟨21, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (83344765406607 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111898472637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_22 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (20827594502557 / 25000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223800906173 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨22, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (20827594502557 / 25000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223800906173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_23 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (83276014720957 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111902478993 / 50000000000000 : ℝ))
      (E := (cell12933 ⟨23, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (83276014720957 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111902478993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_24 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (41620837753139 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223808928783 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨24, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (41620837753139 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223808928783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_25 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (20801840083461 / 25000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223812938203 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨25, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (20801840083461 / 25000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223812938203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_26 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (8317306917147 / 10000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223816930521 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨26, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (8317306917147 / 10000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223816930521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_27 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (83138801987139 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (555955241653 / 25000000000000 : ℝ))
      (E := (cell12933 ⟨27, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (83138801987139 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (555955241653 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_28 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (16620911749799 / 20000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223824990239 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨28, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (16620911749799 / 20000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223824990239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_29 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (41535169712673 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223828944841 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨29, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (41535169712673 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223828944841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_30 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (83036143984663 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (138989559321 / 6250000000000 : ℝ))
      (E := (cell12933 ⟨30, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (83036143984663 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (138989559321 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_31 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (83001972395573 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223837004689 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨31, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (83001972395573 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223837004689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_32 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (20741956156717 / 25000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223840995669 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨32, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (20741956156717 / 25000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223840995669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_33 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (16586740129499 / 20000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (555961245413 / 25000000000000 : ℝ))
      (E := (cell12933 ⟨33, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (16586740129499 / 20000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (555961245413 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_34 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (259061251333 / 312500000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (555962255519 / 25000000000000 : ℝ))
      (E := (cell12933 ⟨34, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (259061251333 / 312500000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (555962255519 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_35 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (41432761966663 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111926500149 / 50000000000000 : ℝ))
      (E := (cell12933 ⟨35, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (41432761966663 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111926500149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_36 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (8283147113721 / 10000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223857033961 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨36, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (8283147113721 / 10000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223857033961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_37 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (41398721003893 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (55596525147 / 2500000000000 : ℝ))
      (E := (cell12933 ⟨37, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (41398721003893 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (55596525147 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_38 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (41381718257391 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223865033347 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨38, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (41381718257391 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223865033347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_39 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (20682363657019 / 25000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111934528693 / 50000000000000 : ℝ))
      (E := (cell12933 ⟨39, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (20682363657019 / 25000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111934528693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12934_20 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (16675833699367 / 20000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (277959628131 / 12500000000000 : ℝ))
      (E := (cell12934 ⟨20, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (16675833699367 / 20000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (277959628131 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_21 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (2083618931581 / 2500000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223681065897 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨21, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (2083618931581 / 2500000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223681065897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_22 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (16662074033803 / 20000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (444737015663 / 20000000000000 : ℝ))
      (E := (cell12934 ⟨22, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (16662074033803 / 20000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (444737015663 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_23 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (41638003590739 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223689065647 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨23, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (41638003590739 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223689065647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_24 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (41620834134057 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223693089399 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨24, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (41620834134057 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223693089399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_25 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (3328294135863 / 4000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223697094099 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨25, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (3328294135863 / 4000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223697094099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_26 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (83173062534679 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (222370108239 / 10000000000000 : ℝ))
      (E := (cell12934 ⟨26, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (83173062534679 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (222370108239 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_27 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (83138795650409 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223705056681 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨27, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (83138795650409 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223705056681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_28 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (8310455271191 / 10000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223709077641 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨28, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (8310455271191 / 10000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223709077641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_29 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (83070333687491 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111856544389 / 50000000000000 : ℝ))
      (E := (cell12934 ⟨29, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (83070333687491 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111856544389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_30 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (83036138545623 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (222371709181 / 10000000000000 : ℝ))
      (E := (cell12934 ⟨30, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (83036138545623 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (222371709181 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_31 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (16600393450987 / 20000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (222372108823 / 10000000000000 : ℝ))
      (E := (cell12934 ⟨31, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (16600393450987 / 20000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (222372108823 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_32 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (41483909892109 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (444745027577 / 20000000000000 : ℝ))
      (E := (cell12934 ⟨32, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (41483909892109 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (444745027577 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_33 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (82933696102421 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (222372912467 / 10000000000000 : ℝ))
      (E := (cell12934 ⟨33, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (82933696102421 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (222372912467 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_34 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (82899596178651 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (555933276989 / 25000000000000 : ℝ))
      (E := (cell12934 ⟨34, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (82899596178651 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (555933276989 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_35 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (82865519982171 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111868573491 / 50000000000000 : ℝ))
      (E := (cell12934 ⟨35, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (82865519982171 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111868573491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_36 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (103539334353 / 125000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (69491910151 / 3125000000000 : ℝ))
      (E := (cell12934 ⟨36, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (103539334353 / 125000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (69491910151 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_37 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (82797438648911 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111872579487 / 50000000000000 : ℝ))
      (E := (cell12934 ⟨37, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (82797438648911 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111872579487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_38 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (41381716725717 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223749131949 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨38, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (41381716725717 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223749131949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_39 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (10341181482481 / 12500000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111876580439 / 50000000000000 : ℝ))
      (E := (cell12934 ⟨39, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (10341181482481 / 12500000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (1111876580439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12935_20 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (83379160052419 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111780603897 / 50000000000000 : ℝ))
      (E := (cell12935 ⟨20, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (83379160052419 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111780603897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_21 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (83344749121363 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111782591427 / 50000000000000 : ℝ))
      (E := (cell12935 ⟨21, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (83344749121363 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111782591427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_22 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (10413795291157 / 12500000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (3474326857 / 156250000000 : ℝ))
      (E := (cell12935 ⟨22, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (10413795291157 / 12500000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (3474326857 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_23 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (10409499955427 / 12500000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223573228089 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨23, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (10409499955427 / 12500000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223573228089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_24 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (83241661031331 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111788623231 / 50000000000000 : ℝ))
      (E := (cell12935 ⟨24, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (83241661031331 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111788623231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_25 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (20801836615163 / 25000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111790623239 / 50000000000000 : ℝ))
      (E := (cell12935 ⟨25, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (20801836615163 / 25000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111790623239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_26 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (41586527949599 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223585230777 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨26, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (41586527949599 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223585230777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_27 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (83138789314953 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (444717852047 / 20000000000000 : ℝ))
      (E := (cell12935 ⟨27, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (83138789314953 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (444717852047 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_28 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (2597017083627 / 3125000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111796610061 / 50000000000000 : ℝ))
      (E := (cell12935 ⟨28, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (2597017083627 / 3125000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111796610061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_29 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (83070327950839 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223597229343 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨29, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (83070327950839 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223597229343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_30 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (332144532431 / 400000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223601231149 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨30, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (332144532431 / 400000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223601231149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_31 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (20750490528857 / 25000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223605285591 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨31, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (20750490528857 / 25000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223605285591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_32 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (10370976867833 / 12500000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111804638419 / 50000000000000 : ℝ))
      (E := (cell12935 ⟨32, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (10370976867833 / 12500000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111804638419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_33 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (10366711444801 / 12500000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111806632231 / 50000000000000 : ℝ))
      (E := (cell12935 ⟨33, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (10366711444801 / 12500000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111806632231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_34 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (82899591931767 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (8686005109 / 390625000000 : ℝ))
      (E := (cell12935 ⟨34, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (82899591931767 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (8686005109 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_35 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (41432758016003 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111810645257 / 50000000000000 : ℝ))
      (E := (cell12935 ⟨35, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (41432758016003 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111810645257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_36 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (1294241622321 / 1562500000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111812635631 / 50000000000000 : ℝ))
      (E := (cell12935 ⟨36, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (1294241622321 / 1562500000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111812635631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_37 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (20699358822739 / 25000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (444725861797 / 20000000000000 : ℝ))
      (E := (cell12935 ⟨37, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (20699358822739 / 25000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (444725861797 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_38 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (8276343038897 / 10000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (555908321557 / 25000000000000 : ℝ))
      (E := (cell12935 ⟨38, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (8276343038897 / 10000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (555908321557 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_39 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (82729449092469 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223637320107 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨39, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (82729449092469 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223637320107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12936_20 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (83379151609527 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223445386841 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨20, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (83379151609527 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223445386841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_21 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (41672370490487 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223449354473 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨21, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (41672370490487 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223449354473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_22 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (83310354490949 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (444690682343 / 20000000000000 : ℝ))
      (E := (cell12936 ⟨22, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (83310354490949 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (444690682343 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_23 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (20818998026693 / 25000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111728693469 / 50000000000000 : ℝ))
      (E := (cell12936 ⟨23, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (20818998026693 / 25000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111728693469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_24 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (83241653795929 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223461399971 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨24, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (83241653795929 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223461399971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_25 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (41603669763037 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223465395339 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨25, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (41603669763037 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223465395339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_26 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (83173049265027 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111734717063 / 50000000000000 : ℝ))
      (E := (cell12936 ⟨26, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (83173049265027 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111734717063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_27 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (20784695745193 / 25000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223473401879 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨27, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (20784695745193 / 25000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223473401879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_28 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (5194033790091 / 6250000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (444695483537 / 20000000000000 : ℝ))
      (E := (cell12936 ⟨28, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (5194033790091 / 6250000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (444695483537 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_29 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (83070322215389 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223481425049 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨29, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (83070322215389 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223481425049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_30 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (20759031917761 / 25000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223485425689 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨30, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (20759031917761 / 25000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223485425689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_31 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (20750489244263 / 25000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (444697884219 / 20000000000000 : ℝ))
      (E := (cell12936 ⟨31, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (20750489244263 / 25000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (444697884219 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_32 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (41483905051103 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (277936683889 / 12500000000000 : ℝ))
      (E := (cell12936 ⟨32, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (41483905051103 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (277936683889 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_33 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (16586737403091 / 20000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (444699491927 / 20000000000000 : ℝ))
      (E := (cell12936 ⟨33, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (16586737403091 / 20000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (444699491927 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_34 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (82899587685909 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223501446033 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨34, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (82899587685909 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223501446033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_35 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (82865512082831 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (444701097909 / 20000000000000 : ℝ))
      (E := (cell12936 ⟨35, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (82865512082831 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (444701097909 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_36 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (82831460175643 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (8894037893 / 400000000000 : ℝ))
      (E := (cell12936 ⟨36, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (82831460175643 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (8894037893 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_37 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (517483949587 / 625000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223513455917 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨37, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (517483949587 / 625000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223513455917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_38 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (82763427327391 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (444703499237 / 20000000000000 : ℝ))
      (E := (cell12936 ⟨38, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (82763427327391 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (444703499237 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_39 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (82729446325939 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223521476327 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨39, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (82729446325939 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223521476327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12937_20 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (521119644801 / 625000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223329562187 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨20, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (521119644801 / 625000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223329562187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_21 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (3333789313683 / 4000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223333580751 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨21, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (3333789313683 / 4000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223333580751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_22 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (5206896665881 / 6250000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (88933502919 / 4000000000000 : ℝ))
      (E := (cell12937 ⟨22, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (5206896665881 / 6250000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (88933502919 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_23 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (10409498071443 / 12500000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223341600571 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨23, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (10409498071443 / 12500000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223341600571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_24 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (20810411640477 / 25000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223345608323 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨24, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (20810411640477 / 25000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223345608323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_25 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (83207332592841 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (17369918743 / 781250000000 : ℝ))
      (E := (cell12937 ⟨25, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (83207332592841 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (17369918743 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_26 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (16634608526433 / 20000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (444670726799 / 20000000000000 : ℝ))
      (E := (cell12937 ⟨26, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (16634608526433 / 20000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (444670726799 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_27 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (10392347080983 / 12500000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223357598547 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨27, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (10392347080983 / 12500000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223357598547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_28 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (41552267304043 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111680805921 / 50000000000000 : ℝ))
      (E := (cell12937 ⟨28, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (41552267304043 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111680805921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_29 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (41535158240571 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111682808693 / 50000000000000 : ℝ))
      (E := (cell12937 ⟨29, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (41535158240571 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111682808693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_30 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (16607224447101 / 20000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (4342518783 / 195312500000 : ℝ))
      (E := (cell12937 ⟨30, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (16607224447101 / 20000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (4342518783 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_31 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (1296905497497 / 1562500000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223373611861 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨31, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (1296905497497 / 1562500000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223373611861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_32 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (20741951315711 / 25000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (17787021297 / 800000000000 : ℝ))
      (E := (cell12937 ⟨32, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (20741951315711 / 25000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (17787021297 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_33 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (82933682473563 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (17370169153 / 781250000000 : ℝ))
      (E := (cell12937 ⟨33, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (82933682473563 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (17370169153 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_34 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (3315983337643 / 4000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (555846409901 / 25000000000000 : ℝ))
      (E := (cell12937 ⟨34, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (3315983337643 / 4000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (555846409901 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_35 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (41432754067323 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223389685423 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨35, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (41432754067323 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223389685423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_36 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (82831456523697 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111696836061 / 50000000000000 : ℝ))
      (E := (cell12937 ⟨36, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (82831456523697 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111696836061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_37 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (82797428577803 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223397658467 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨37, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (82797428577803 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223397658467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_38 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (10345428033337 / 12500000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223401703097 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨38, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (10345428033337 / 12500000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223401703097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_39 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (41364721780129 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111702844143 / 50000000000000 : ℝ))
      (E := (cell12937 ⟨39, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (41364721780129 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111702844143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12938_20 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (41689567364159 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (444642758427 / 20000000000000 : ℝ))
      (E := (cell12938 ⟨20, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (41689567364159 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (444642758427 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_21 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (83344724704663 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223217803369 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨21, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (83344724704663 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223217803369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_22 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (16662067763739 / 20000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111610894479 / 50000000000000 : ℝ))
      (E := (cell12938 ⟨22, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (16662067763739 / 20000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111610894479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_23 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (83275977037733 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (444645162123 / 20000000000000 : ℝ))
      (E := (cell12938 ⟨23, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (83275977037733 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (444645162123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_24 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (20810409832317 / 25000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111614906561 / 50000000000000 : ℝ))
      (E := (cell12938 ⟨24, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (20810409832317 / 25000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111614906561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_25 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (41603662830477 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (222323385777 / 10000000000000 : ℝ))
      (E := (cell12938 ⟨25, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (41603662830477 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (222323385777 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_26 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (20793259000153 / 25000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111618915193 / 50000000000000 : ℝ))
      (E := (cell12938 ⟨26, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (20793259000153 / 25000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111618915193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_27 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (83138770316229 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223241850237 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨27, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (83138770316229 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223241850237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_28 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (83104528575953 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111622930541 / 50000000000000 : ℝ))
      (E := (cell12938 ⟨28, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (83104528575953 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111622930541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_29 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (1297973605439 / 1562500000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111624932433 / 50000000000000 : ℝ))
      (E := (cell12938 ⟨29, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (1297973605439 / 1562500000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111624932433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_30 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (20759029200283 / 25000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (444650772661 / 20000000000000 : ℝ))
      (E := (cell12938 ⟨30, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (20759029200283 / 25000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (444650772661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_31 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (41500973351847 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (222325785789 / 10000000000000 : ℝ))
      (E := (cell12938 ⟨31, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (41500973351847 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (222325785789 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_32 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (82967800424577 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223261849879 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨32, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (82967800424577 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223261849879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_33 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (82933677932731 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111632949457 / 50000000000000 : ℝ))
      (E := (cell12938 ⟨33, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (82933677932731 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111632949457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_34 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (41449789598633 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (277908736077 / 12500000000000 : ℝ))
      (E := (cell12938 ⟨34, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (41449789598633 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (277908736077 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_35 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (1657310083749 / 2000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223273878151 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨35, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (1657310083749 / 2000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223273878151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_36 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (10111261337 / 12207031250 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (444655585311 / 20000000000000 : ℝ))
      (E := (cell12938 ⟨36, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (10111261337 / 12207031250 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (444655585311 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_37 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (16559485044521 / 20000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111640958319 / 50000000000000 : ℝ))
      (E := (cell12938 ⟨37, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (16559485044521 / 20000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111640958319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_38 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (16552684241377 / 20000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223285906967 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨38, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (16552684241377 / 20000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223285906967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_39 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (41364720397713 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223289897237 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨39, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (41364720397713 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223289897237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12939_20 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (8337912629 / 10000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111549038343 / 50000000000000 : ℝ))
      (E := (cell12939 ⟨20, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (8337912629 / 10000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111549038343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_21 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (4167235828437 / 5000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (44462041613 / 2000000000000 : ℝ))
      (E := (cell12939 ⟨21, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (4167235828437 / 5000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (44462041613 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_22 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (16662066196949 / 20000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (444621211933 / 20000000000000 : ℝ))
      (E := (cell12939 ⟨22, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (16662066196949 / 20000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (444621211933 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_23 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (41637984752669 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223110075443 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨23, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (41637984752669 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223110075443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_24 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (83241632098007 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111557036383 / 50000000000000 : ℝ))
      (E := (cell12939 ⟨24, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (83241632098007 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111557036383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_25 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (8320731873041 / 10000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (444623610901 / 20000000000000 : ℝ))
      (E := (cell12939 ⟨25, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (8320731873041 / 10000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (444623610901 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_26 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (162447322989 / 195312500000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223122081741 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨26, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (162447322989 / 195312500000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223122081741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_27 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (83138763985867 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223126098487 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨27, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (83138763985867 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223126098487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_28 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (41552261272529 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223130106917 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨28, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (41552261272529 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223130106917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_29 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (83070305016253 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223134108977 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨29, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (83070305016253 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223134108977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_30 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (41518055683963 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223138106383 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨30, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (41518055683963 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223138106383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_31 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (10375242696089 / 12500000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111571050311 / 50000000000000 : ℝ))
      (E := (cell12939 ⟨31, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (10375242696089 / 12500000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111571050311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_32 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (16593559117481 / 20000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111573075769 / 50000000000000 : ℝ))
      (E := (cell12939 ⟨32, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (16593559117481 / 20000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111573075769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_33 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (41466836696479 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111575071511 / 50000000000000 : ℝ))
      (E := (cell12939 ⟨33, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (41466836696479 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111575071511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_34 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (41449787477241 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111577067221 / 50000000000000 : ℝ))
      (E := (cell12939 ⟨34, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (41449787477241 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111577067221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_35 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (82865500241243 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223158126381 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨35, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (82865500241243 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223158126381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_36 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (16566289844533 / 20000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (17785297423 / 800000000000 : ℝ))
      (E := (cell12939 ⟨36, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (16566289844533 / 20000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (17785297423 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_37 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (41398710934163 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223166171731 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨37, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (41398710934163 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223166171731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_38 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (82763418147957 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111585083259 / 50000000000000 : ℝ))
      (E := (cell12939 ⟨38, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (82763418147957 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111585083259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_39 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (41364719015721 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (277896770241 / 12500000000000 : ℝ))
      (E := (cell12939 ⟨39, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (41364719015721 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (277896770241 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12940_20 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (16675823570641 / 20000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (111149117877 / 5000000000000 : ℝ))
      (E := (cell12940 ⟨20, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (16675823570641 / 20000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (111149117877 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_21 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (651130534643 / 781250000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2222986354271 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨21, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (651130534643 / 781250000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2222986354271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_22 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (10413790394031 / 12500000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (555747581687 / 25000000000000 : ℝ))
      (E := (cell12940 ⟨22, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (10413790394031 / 12500000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (555747581687 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_23 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (83275961974359 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (555748584171 / 25000000000000 : ℝ))
      (E := (cell12940 ⟨23, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (83275961974359 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (555748584171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_24 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (83241624868127 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (111149916443 / 5000000000000 : ℝ))
      (E := (cell12940 ⟨24, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (83241624868127 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (111149916443 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_25 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (83207311801211 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223002364563 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨25, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (83207311801211 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223002364563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_26 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (10396627842679 / 12500000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111503194031 / 50000000000000 : ℝ))
      (E := (cell12940 ⟨26, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (10396627842679 / 12500000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111503194031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_27 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (41569378828389 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223010343297 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨27, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (41569378828389 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223010343297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_28 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (83104516515399 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111507203919 / 50000000000000 : ℝ))
      (E := (cell12940 ⟨28, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (83104516515399 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111507203919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_29 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (8307029928561 / 10000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111509204117 / 50000000000000 : ℝ))
      (E := (cell12940 ⟨29, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (8307029928561 / 10000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111509204117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_30 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (16607221187177 / 20000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111511202333 / 50000000000000 : ℝ))
      (E := (cell12940 ⟨30, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (16607221187177 / 20000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111511202333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_31 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (83001936434859 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223026398621 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨31, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (83001936434859 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223026398621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_32 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (2592743460979 / 3125000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223030391357 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨32, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (2592743460979 / 3125000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223030391357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_33 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (16586733770849 / 20000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (555758595977 / 25000000000000 : ℝ))
      (E := (cell12940 ⟨33, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (16586733770849 / 20000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (555758595977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_34 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (82899570712721 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (17367487779 / 781250000000 : ℝ))
      (E := (cell12940 ⟨34, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (82899570712721 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (17367487779 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_35 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (3314619851841 / 4000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111521215057 / 50000000000000 : ℝ))
      (E := (cell12940 ⟨35, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (3314619851841 / 4000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111521215057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_36 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (4141572278679 / 5000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223046426081 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨36, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (4141572278679 / 5000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223046426081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_37 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (16559483702993 / 20000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223050423747 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨37, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (16559483702993 / 20000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223050423747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_38 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (10345426886239 / 12500000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223054423027 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨38, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (10345426886239 / 12500000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223054423027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_39 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (41364717634153 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223058482361 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨39, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (41364717634153 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223058482361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12941_20 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (83379109417933 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111433317349 / 50000000000000 : ℝ))
      (E := (cell12941 ⟨20, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (83379109417933 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111433317349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_21 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (20836175075339 / 25000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (277858828029 / 12500000000000 : ℝ))
      (E := (cell12941 ⟨21, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (20836175075339 / 25000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (277858828029 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_22 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (83310315321201 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222874648557 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨22, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (83310315321201 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222874648557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_23 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (16655190888959 / 20000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222878652711 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨23, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (16655190888959 / 20000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222878652711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_24 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (41620808819813 / 50000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222882639799 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨24, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (41620808819813 / 50000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222882639799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_25 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (16641460974671 / 20000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (555721667777 / 25000000000000 : ℝ))
      (E := (cell12941 ⟨25, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (16641460974671 / 20000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (555721667777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_26 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (20793254028451 / 25000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111445345453 / 50000000000000 : ℝ))
      (E := (cell12941 ⟨26, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (20793254028451 / 25000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111445345453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_27 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (259808597903 / 312500000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111447350799 / 50000000000000 : ℝ))
      (E := (cell12941 ⟨27, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (259808597903 / 312500000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111447350799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_28 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (83104510486977 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (555724676339 / 25000000000000 : ℝ))
      (E := (cell12941 ⟨28, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (83104510486977 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (555724676339 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_29 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (10383786694521 / 12500000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (17783221633 / 800000000000 : ℝ))
      (E := (cell12941 ⟨29, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (10383786694521 / 12500000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (17783221633 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_30 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (83036100505009 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222906699619 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨30, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (83036100505009 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222906699619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_31 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (10375241412767 / 12500000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (88916427733 / 4000000000000 : ℝ))
      (E := (cell12941 ⟨31, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (10375241412767 / 12500000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (88916427733 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_32 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (16593557183269 / 20000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222914686501 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨32, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (16593557183269 / 20000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222914686501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_33 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (8293366431659 / 10000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111459369393 / 50000000000000 : ℝ))
      (E := (cell12941 ⟨33, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (8293366431659 / 10000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111459369393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_34 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (5181222904499 / 6250000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (555730683449 / 25000000000000 : ℝ))
      (E := (cell12941 ⟨34, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (5181222904499 / 6250000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (555730683449 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_35 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (16573098470359 / 20000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222926730699 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨35, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (16573098470359 / 20000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222926730699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_36 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (10353930240681 / 12500000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222930729849 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨36, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (10353930240681 / 12500000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222930729849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_37 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (41398707581261 / 50000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (444586946277 / 20000000000000 : ℝ))
      (E := (cell12941 ⟨37, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (41398707581261 / 50000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (444586946277 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_38 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (331053648131 / 400000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111469367609 / 50000000000000 : ℝ))
      (E := (cell12941 ⟨38, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (331053648131 / 400000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111469367609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_39 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (41364716253009 / 50000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222942741041 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨39, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (41364716253009 / 50000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222942741041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12942_20 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (16675820196837 / 20000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222750966461 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨20, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (16675820196837 / 20000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222750966461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_21 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (41672346084947 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222754948859 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨21, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (41672346084947 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222754948859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_22 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (41655153745803 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (277844870843 / 12500000000000 : ℝ))
      (E := (cell12942 ⟨22, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (41655153745803 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (277844870843 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_23 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (41637973458323 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (69461342661 / 3125000000000 : ℝ))
      (E := (cell12942 ⟨23, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (41637973458323 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (69461342661 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_24 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (16648322082501 / 20000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (444553401117 / 20000000000000 : ℝ))
      (E := (cell12942 ⟨24, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (16648322082501 / 20000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (444553401117 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_25 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (41603648973421 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222770974143 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨25, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (41603648973421 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222770974143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_26 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (83173009487483 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555693747569 / 25000000000000 : ℝ))
      (E := (cell12942 ⟨26, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (83173009487483 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555693747569 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_27 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (16627749000483 / 20000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (444555799599 / 20000000000000 : ℝ))
      (E := (cell12942 ⟨27, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (16627749000483 / 20000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (444555799599 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_28 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (5194031528737 / 6250000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222782999471 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨28, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (5194031528737 / 6250000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222782999471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_29 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (83070287827927 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (44455739933 / 2000000000000 : ℝ))
      (E := (cell12942 ⟨29, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (83070287827927 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (44455739933 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_30 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (83036095075299 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (1111395524889 / 50000000000000 : ℝ))
      (E := (cell12942 ⟨30, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (83036095075299 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (1111395524889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_31 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (83001926170543 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (444559008659 / 20000000000000 : ℝ))
      (E := (cell12942 ⟨31, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (83001926170543 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (444559008659 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_32 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (82967781082457 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (222279903697 / 10000000000000 : ℝ))
      (E := (cell12942 ⟨32, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (82967781082457 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (222279903697 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_33 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (16586731955999 / 20000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555700757959 / 25000000000000 : ℝ))
      (E := (cell12942 ⟨33, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (16586731955999 / 20000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555700757959 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_34 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (82899562232271 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222807028697 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨34, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (82899562232271 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222807028697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_35 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (41432744204277 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (1111405514067 / 50000000000000 : ℝ))
      (E := (cell12942 ⟨35, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (41432744204277 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (1111405514067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_36 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (82831438278269 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222815089183 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨36, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (82831438278269 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222815089183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_37 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (82797411810997 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222819094647 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨37, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (82797411810997 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222819094647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_38 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (82763408976471 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555705775773 / 25000000000000 : ℝ))
      (E := (cell12942 ⟨38, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (82763408976471 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555705775773 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_39 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (41364714872289 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222827114211 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨39, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (41364714872289 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222827114211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12943_20 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (83379092551959 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222635294531 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨20, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (83379092551959 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222635294531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_21 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (83344684039919 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111319664077 / 50000000000000 : ℝ))
      (E := (cell12943 ⟨21, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (83344684039919 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111319664077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_22 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (83310299663461 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222643339659 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨22, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (83310299663461 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222643339659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_23 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (83275939389911 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222647332383 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨23, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (83275939389911 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222647332383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_24 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (41620801593381 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222651309429 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨24, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (41620801593381 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222651309429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_25 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (83207291021673 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (444531066417 / 20000000000000 : ℝ))
      (E := (cell12943 ⟨25, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (83207291021673 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (444531066417 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_26 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (8317300286247 / 10000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111329672307 / 50000000000000 : ℝ))
      (E := (cell12943 ⟨26, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (8317300286247 / 10000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111329672307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_27 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (41569369338571 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (111133167471 / 5000000000000 : ℝ))
      (E := (cell12943 ⟨27, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (41569369338571 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (111133167471 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_28 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (41552249216921 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (555666837169 / 25000000000000 : ℝ))
      (E := (cell12943 ⟨28, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (41552249216921 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (555666837169 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_29 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (83070282100887 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222671344323 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨29, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (83070282100887 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222671344323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_30 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (83036089646753 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222675396611 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨30, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (83036089646753 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222675396611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_31 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (83001921040079 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (88907175599 / 4000000000000 : ℝ))
      (E := (cell12943 ⟨31, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (83001921040079 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (88907175599 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_32 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (41483888124831 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111341692093 / 50000000000000 : ℝ))
      (E := (cell12943 ⟨32, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (41483888124831 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111341692093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_33 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (41466827622229 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111343690137 / 50000000000000 : ℝ))
      (E := (cell12943 ⟨33, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (41466827622229 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111343690137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_34 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (82899557993581 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (555672844761 / 25000000000000 : ℝ))
      (E := (cell12943 ⟨34, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (82899557993581 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (555672844761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_35 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (828654844663 / 1000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222695381077 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨35, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (828654844663 / 1000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222695381077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_36 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (82831434632043 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222699386729 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨36, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (82831434632043 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222699386729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_37 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (82797408460389 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (444540679227 / 20000000000000 : ℝ))
      (E := (cell12943 ⟨37, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (82797408460389 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (444540679227 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_38 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (41381702960537 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (444541481841 / 20000000000000 : ℝ))
      (E := (cell12943 ⟨38, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (41381702960537 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (444541481841 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_39 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (16545885396797 / 20000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222711425631 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨39, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (16545885396797 / 20000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222711425631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12944_20 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (16675816824251 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222519677209 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨20, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (16675816824251 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222519677209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_21 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (8334467591143 / 10000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222523703793 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨21, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (8334467591143 / 10000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222523703793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_22 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (41655145918383 / 50000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (444505541791 / 20000000000000 : ℝ))
      (E := (cell12944 ⟨22, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (41655145918383 / 50000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (444505541791 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_23 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (83275931864591 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (222253169603 / 10000000000000 : ℝ))
      (E := (cell12944 ⟨23, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (83275931864591 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (222253169603 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_24 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (41620797981199 / 50000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222535726517 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨24, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (41620797981199 / 50000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222535726517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_25 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (41603642048923 / 50000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222539744937 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨25, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (41603642048923 / 50000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222539744937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_26 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (83172996238763 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222543753921 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨26, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (83172996238763 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222543753921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_27 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (83138732353139 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (17780382047 / 800000000000 : ℝ))
      (E := (cell12944 ⟨27, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (83138732353139 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (17780382047 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_28 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (10388061551141 / 12500000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222551752969 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨28, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (10388061551141 / 12500000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222551752969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_29 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (41535138187523 / 50000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (444511149429 / 20000000000000 : ℝ))
      (E := (cell12944 ⟨29, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (41535138187523 / 50000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (444511149429 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_30 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (20759021054843 / 25000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (444511948023 / 20000000000000 : ℝ))
      (E := (cell12944 ⟨30, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (20759021054843 / 25000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (444511948023 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_31 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (10375239488843 / 12500000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (555640933341 / 25000000000000 : ℝ))
      (E := (cell12944 ⟨31, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (10375239488843 / 12500000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (555640933341 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_32 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (82967771417961 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222567786729 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨32, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (82967771417961 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222567786729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_33 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (4146682535499 / 5000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (1111285892049 / 50000000000000 : ℝ))
      (E := (cell12944 ⟨33, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (4146682535499 / 5000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (1111285892049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_34 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (41449776877957 / 50000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (1111287892419 / 50000000000000 : ℝ))
      (E := (cell12944 ⟨34, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (41449776877957 / 50000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (1111287892419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_35 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (16573096105007 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (88903191581 / 4000000000000 : ℝ))
      (E := (cell12944 ⟨35, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (16573096105007 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (88903191581 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_36 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (82831430986769 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (1111291899259 / 50000000000000 : ℝ))
      (E := (cell12944 ⟨36, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (82831430986769 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (1111291899259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_37 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (82797405110699 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (555646952987 / 25000000000000 : ℝ))
      (E := (cell12944 ⟨37, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (82797405110699 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (555646952987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_38 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (129317816979 / 156250000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (1111295914863 / 50000000000000 : ℝ))
      (E := (cell12944 ⟨38, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (129317816979 / 156250000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (1111295914863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_39 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (82729424224239 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (555648948199 / 25000000000000 : ℝ))
      (E := (cell12944 ⟨39, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (82729424224239 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (555648948199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12945_20 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (83379075692073 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (444480822899 / 20000000000000 : ℝ))
      (E := (cell12945 ⟨20, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (83379075692073 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (444480822899 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_21 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (83344667784427 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (88896323031 / 4000000000000 : ℝ))
      (E := (cell12945 ⟨21, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (83344667784427 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (88896323031 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_22 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (41655142005761 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222412132979 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨22, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (41655142005761 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222412132979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_23 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (16655184868137 / 20000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222416114467 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨23, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (16655184868137 / 20000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222416114467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_24 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (83241588739411 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222420140061 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨24, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (83241588739411 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222420140061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_25 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (41603638587681 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (111121204793 / 5000000000000 : ℝ))
      (E := (cell12945 ⟨25, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (41603638587681 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (111121204793 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_26 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (83172989616363 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111214050657 / 50000000000000 : ℝ))
      (E := (cell12945 ⟨26, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (83172989616363 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111214050657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_27 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (10392340753801 / 12500000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222432158893 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨27, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (10392340753801 / 12500000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222432158893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_28 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (83104486385649 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111218076931 / 50000000000000 : ℝ))
      (E := (cell12945 ⟨28, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (83104486385649 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111218076931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_29 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (16614054130081 / 20000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (555610036651 / 25000000000000 : ℝ))
      (E := (cell12945 ⟨29, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (16614054130081 / 20000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (555610036651 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_30 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (16607215758631 / 20000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222444138829 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨30, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (16607215758631 / 20000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222444138829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_31 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (41500955391269 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222448132021 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨31, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (41500955391269 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222448132021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_32 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (41483883293677 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222452186017 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨32, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (41483883293677 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222452186017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_33 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (82933646176559 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111228092353 / 50000000000000 : ℝ))
      (E := (cell12945 ⟨33, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (82933646176559 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111228092353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_34 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (82899549519269 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222460187451 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨34, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (82899549519269 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222460187451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_35 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (20716369146189 / 25000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222464194829 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨35, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (20716369146189 / 25000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222464194829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_36 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (5176964208903 / 6250000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222468207197 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨36, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (5176964208903 / 6250000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222468207197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_37 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (41398700880963 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222472224687 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨37, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (41398700880963 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222472224687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_38 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (82763399812927 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111238094243 / 50000000000000 : ℝ))
      (E := (cell12945 ⟨38, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (82763399812927 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111238094243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_39 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (4136471073267 / 5000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111240107853 / 50000000000000 : ℝ))
      (E := (cell12945 ⟨39, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (4136471073267 / 5000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111240107853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12946_20 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (20844766816103 / 25000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222288548091 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨20, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (20844766816103 / 25000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222288548091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_21 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (83344659658909 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222292502429 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨21, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (83344659658909 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222292502429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_22 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (41655138093863 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222296553387 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨22, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (41655138093863 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222296553387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_23 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (5204744801137 / 6250000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222300529323 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨23, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (5204744801137 / 6250000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222300529323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_24 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (83241581517803 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222304550059 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨24, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (83241581517803 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222304550059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_25 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (83207270254219 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (1111154280057 / 50000000000000 : ℝ))
      (E := (cell12946 ⟨25, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (83207270254219 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (1111154280057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_26 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (8317298299527 / 10000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222312562119 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨26, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (8317298299527 / 10000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222312562119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_27 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (83138719708947 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222316558477 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨27, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (83138719708947 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222316558477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_28 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (16620896072681 / 20000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (1111160275679 / 50000000000000 : ℝ))
      (E := (cell12946 ⟨28, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (16620896072681 / 20000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (1111160275679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_29 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (20767566231741 / 25000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222324601213 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨29, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (20767566231741 / 25000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222324601213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_30 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (41518036684051 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222328592753 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨30, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (41518036684051 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222328592753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_31 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (83001905655461 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (555583146487 / 25000000000000 : ℝ))
      (E := (cell12946 ⟨31, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (83001905655461 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (555583146487 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_32 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (82967761757839 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222336582053 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨32, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (82967761757839 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222336582053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_33 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (20733410411049 / 25000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222340582097 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨33, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (20733410411049 / 25000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222340582097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_34 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (82899545283647 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222344586883 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨34, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (82899545283647 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222344586883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_35 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (16573094529093 / 20000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (555587149247 / 25000000000000 : ℝ))
      (E := (cell12946 ⟨35, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (16573094529093 / 20000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (555587149247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_36 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (41415711849539 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (69448519149 / 3125000000000 : ℝ))
      (E := (cell12946 ⟨36, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (41415711849539 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (69448519149 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_37 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (82797398414069 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (444471326871 / 20000000000000 : ℝ))
      (E := (cell12946 ⟨37, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (82797398414069 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (444471326871 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_38 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (5172712297511 / 6250000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (277795082707 / 12500000000000 : ℝ))
      (E := (cell12946 ⟨38, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (5172712297511 / 6250000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (277795082707 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_39 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (10341177338411 / 12500000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (444472927123 / 20000000000000 : ℝ))
      (E := (cell12946 ⟨39, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (10341177338411 / 12500000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (444472927123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12947_20 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (325699448587 / 390625000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (555543244499 / 25000000000000 : ℝ))
      (E := (cell12947 ⟨20, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (325699448587 / 390625000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (555543244499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_21 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (20836162883719 / 25000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111088491877 / 50000000000000 : ℝ))
      (E := (cell12947 ⟨21, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (20836162883719 / 25000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111088491877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_22 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (4165513418269 / 5000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222180970177 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨22, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (4165513418269 / 5000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222180970177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_23 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (83275909297113 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222184998971 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨23, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (83275909297113 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222184998971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_24 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (20810393574393 / 25000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (222218901491 / 10000000000000 : ℝ))
      (E := (cell12947 ⟨24, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (20810393574393 / 25000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (222218901491 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_25 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (83207263334419 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (111109651043 / 5000000000000 : ℝ))
      (E := (cell12947 ⟨25, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (83207263334419 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (111109651043 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_26 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (41586488187741 / 50000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (444439403891 / 20000000000000 : ℝ))
      (E := (cell12947 ⟨26, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (41586488187741 / 50000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (444439403891 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_27 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (20784678347189 / 25000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111100506547 / 50000000000000 : ℝ))
      (E := (cell12947 ⟨27, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (20784678347189 / 25000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111100506547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_28 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (20776118585599 / 25000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111102501973 / 50000000000000 : ℝ))
      (E := (cell12947 ⟨28, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (20776118585599 / 25000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111102501973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_29 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (83070259204721 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222209052463 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨29, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (83070259204721 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222209052463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_30 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (83036067944213 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222213043353 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨30, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (83036067944213 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222213043353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_31 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (83001900529511 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (555554259147 / 25000000000000 : ℝ))
      (E := (cell12947 ⟨31, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (83001900529511 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (555554259147 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_32 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (82967756929417 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222221033421 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨32, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (82967756929417 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222221033421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_33 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (8293363711289 / 10000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222225034879 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨33, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (8293363711289 / 10000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222225034879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_34 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (82899541049047 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (444445808353 / 20000000000000 : ℝ))
      (E := (cell12947 ⟨34, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (82899541049047 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (444445808353 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_35 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (2071636717679 / 2500000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111116527329 / 50000000000000 : ℝ))
      (E := (cell12947 ⟨35, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (2071636717679 / 2500000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111116527329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_36 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (4141571002833 / 5000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222237073909 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨36, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (4141571002833 / 5000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222237073909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_37 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (8279739506713 / 10000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (44444821993 / 2000000000000 : ℝ))
      (E := (cell12947 ⟨37, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (8279739506713 / 10000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (44444821993 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_38 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (82763393708307 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222245073067 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨38, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (82763393708307 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222245073067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_39 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (41364707975041 / 50000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (277781138909 / 12500000000000 : ℝ))
      (E := (cell12947 ⟨39, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (41364707975041 / 50000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (277781138909 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12948_20 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (83379050413653 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1111028731257 / 50000000000000 : ℝ))
      (E := (cell12948 ⟨20, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (83379050413653 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1111028731257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_21 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (10418080426541 / 12500000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222061461427 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨21, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (10418080426541 / 12500000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222061461427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_22 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (41655130272241 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222065441701 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨22, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (41655130272241 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222065441701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_23 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (83275901777447 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (27775868313 / 1250000000000 : ℝ))
      (E := (cell12948 ⟨23, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (83275901777447 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (27775868313 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_24 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (41620783539359 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222073476219 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨24, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (41620783539359 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222073476219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_25 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (83207256415959 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1111038739051 / 50000000000000 : ℝ))
      (E := (cell12948 ⟨25, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (83207256415959 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1111038739051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_26 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (83172969757 / 100000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1111040736661 / 50000000000000 : ℝ))
      (E := (cell12948 ⟨26, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (83172969757 / 100000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1111040736661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_27 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (16627741413967 / 20000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222085464277 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨27, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (16627741413967 / 20000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222085464277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_28 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (83104468322621 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222089511627 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨28, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (83104468322621 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222089511627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_29 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (41535126741839 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (34720210943 / 1562500000000 : ℝ))
      (E := (cell12948 ⟨29, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (41535126741839 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (34720210943 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_30 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (83036062521487 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (222209749063 / 10000000000000 : ℝ))
      (E := (cell12948 ⟨30, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (83036062521487 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (222209749063 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_31 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (8300189540469 / 10000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (888840617 / 40000000000 : ℝ))
      (E := (cell12948 ⟨31, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (8300189540469 / 10000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (888840617 / 40000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_32 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (10370969012761 / 12500000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (55552638503 / 2500000000000 : ℝ))
      (E := (cell12948 ⟨32, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (10370969012761 / 12500000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (55552638503 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_33 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (41466816291321 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (555527385763 / 25000000000000 : ℝ))
      (E := (cell12948 ⟨33, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (41466816291321 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (555527385763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_34 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (82899536815469 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222113552099 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨34, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (82899536815469 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222113552099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_35 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (82865464769843 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222117567837 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨35, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (82865464769843 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222117567837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_36 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (82831416415193 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222121531943 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨36, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (82831416415193 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222121531943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_37 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (41398695860553 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (555531390469 / 25000000000000 : ℝ))
      (E := (cell12948 ⟨37, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (41398695860553 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (555531390469 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_38 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (82763390657319 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222129540167 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨38, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (82763390657319 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222129540167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_39 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (82729413193723 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222133583929 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨39, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (82729413193723 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222133583929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12949_20 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (41689520995277 / 50000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1110970971671 / 50000000000000 : ℝ))
      (E := (cell12949 ⟨20, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (41689520995277 / 50000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1110970971671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_21 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (651129963213 / 781250000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221945935447 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨21, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (651129963213 / 781250000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221945935447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_22 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (83310252725033 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221949967957 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨22, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (83310252725033 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221949967957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_23 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (83275894259193 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221953985901 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨23, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (83275894259193 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221953985901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_24 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (2081038996531 / 2500000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221957992381 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨24, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (2081038996531 / 2500000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221957992381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_25 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (2080181237471 / 2500000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221961990257 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨25, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (2080181237471 / 2500000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221961990257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_26 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (83172963139823 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1110982991081 / 50000000000000 : ℝ))
      (E := (cell12949 ⟨26, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (83172963139823 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1110982991081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_27 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (10392337594023 / 12500000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1110984985247 / 50000000000000 : ℝ))
      (E := (cell12949 ⟨27, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (10392337594023 / 12500000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1110984985247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_28 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (1038805778801 / 1250000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221974015911 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨28, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (1038805778801 / 1250000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221974015911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_29 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (83070247763833 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1110989001697 / 50000000000000 : ℝ))
      (E := (cell12949 ⟨29, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (83070247763833 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1110989001697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_30 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (20759014274981 / 25000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1110990996559 / 50000000000000 : ℝ))
      (E := (cell12949 ⟨30, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (20759014274981 / 25000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1110990996559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_31 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (20750472570249 / 25000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555496511281 / 25000000000000 : ℝ))
      (E := (cell12949 ⟨31, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (20750472570249 / 25000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555496511281 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_32 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (82967747275851 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221990043567 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨32, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (82967747275851 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2221990043567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_33 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (1658672561069 / 2000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (222199404801 / 10000000000000 : ℝ))
      (E := (cell12949 ⟨33, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (1658672561069 / 2000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (222199404801 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_34 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (20239143697 / 24414062500 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1110999029627 / 50000000000000 : ℝ))
      (E := (cell12949 ⟨34, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (20239143697 / 24414062500 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1110999029627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_35 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (82865460833511 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (111100100961 / 5000000000000 : ℝ))
      (E := (cell12949 ⟨35, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (82865460833511 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (111100100961 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_36 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (41415706387339 / 50000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1111003022773 / 50000000000000 : ℝ))
      (E := (cell12949 ⟨36, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (41415706387339 / 50000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1111003022773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_37 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (41398694187999 / 50000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222010079731 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨37, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (41398694187999 / 50000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222010079731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_38 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (82763387607211 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222014062957 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨38, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (82763387607211 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222014062957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_39 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (82729410438209 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555504513397 / 25000000000000 : ℝ))
      (E := (cell12949 ⟨39, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (82729410438209 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555504513397 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

end BstLean.Part268
