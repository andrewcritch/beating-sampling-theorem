import BstLean.Part268CellShard0Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12350_20 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (83384373848011 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (114856091581 / 5000000000000 : ℝ))
      (E := (cell12350 ⟨20, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (83384373848011 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (114856091581 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_21 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (41674889761957 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148562908059 / 50000000000000 : ℝ))
      (E := (cell12350 ⟨21, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (41674889761957 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148562908059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_22 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (41657604797323 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (91885192463 / 4000000000000 : ℝ))
      (E := (cell12350 ⟨22, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (41657604797323 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (91885192463 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_23 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (20820166006753 / 25000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (287141727799 / 12500000000000 : ℝ))
      (E := (cell12350 ⟨23, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (20820166006753 / 25000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (287141727799 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_24 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (20811535696997 / 25000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297137852727 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨24, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (20811535696997 / 25000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297137852727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_25 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (1040145573059 / 1250000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297141848143 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨25, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (1040145573059 / 1250000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297141848143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_26 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (3327086926581 / 4000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (459429162451 / 20000000000000 : ℝ))
      (E := (cell12350 ⟨26, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (3327086926581 / 4000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (459429162451 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_27 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (20785681178721 / 25000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (574287451713 / 25000000000000 : ℝ))
      (E := (cell12350 ⟨27, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (20785681178721 / 25000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (574287451713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_28 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (1662166009269 / 2000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148576917573 / 50000000000000 : ℝ))
      (E := (cell12350 ⟨28, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (1662166009269 / 2000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148576917573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_29 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (41536950189019 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (459431556643 / 20000000000000 : ℝ))
      (E := (cell12350 ⟨29, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (41536950189019 / 50000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (459431556643 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_30 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (8303952442663 / 10000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148580914549 / 50000000000000 : ℝ))
      (E := (cell12350 ⟨30, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (8303952442663 / 10000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148580914549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_31 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (83005172577371 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297165799883 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨31, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (83005172577371 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297165799883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_32 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (8297084479857 / 10000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (574292453691 / 25000000000000 : ℝ))
      (E := (cell12350 ⟨32, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (8297084479857 / 10000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (574292453691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_33 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (10367067632337 / 12500000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297173817253 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨33, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (10367067632337 / 12500000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297173817253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_34 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (82902261326381 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (574294452277 / 25000000000000 : ℝ))
      (E := (cell12350 ⟨34, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (82902261326381 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (574294452277 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_35 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (5179250348151 / 6250000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (114859089593 / 5000000000000 : ℝ))
      (E := (cell12350 ⟨35, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (5179250348151 / 6250000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (114859089593 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_36 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (331335095039 / 400000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148592883407 / 50000000000000 : ℝ))
      (E := (cell12350 ⟨36, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (331335095039 / 400000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148592883407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_37 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (20699891465873 / 25000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297189793691 / 100000000000000 : ℝ))
      (E := (cell12350 ⟨37, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (20699891465873 / 25000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (2297189793691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_38 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (82765381850907 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148596878041 / 50000000000000 : ℝ))
      (E := (cell12350 ⟨38, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (82765381850907 / 100000000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (1148596878041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12350_39 : CellCertificate 12350 (896734522306907 / 10000000000000000 : ℝ) (850389652718653 / 500000000000000000 : ℝ) (34378861237447 / 1000000000000000 : ℝ)
    (cell12350 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · norm_num [cell12350]
  · have h := gap_lower (n := 12350) (a := (10341402711427 / 12500000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (91887910877 / 4000000000000 : ℝ))
      (E := (cell12350 ⟨39, by decide⟩).energy) (xi := (34378861237447 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12350 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12350]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12350])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12350) (a := (10341402711427 / 12500000000000 : ℝ)) (b := (41711160531 / 25000000000000 : ℝ)) (q := (91887910877 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12350])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12350]

theorem cert12351_20 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (4169218222189 / 5000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (28712278859 / 1250000000000 : ℝ))
      (E := (cell12351 ⟨20, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (4169218222189 / 5000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (28712278859 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_21 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (83349770444569 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (459397262129 / 20000000000000 : ℝ))
      (E := (cell12351 ⟨21, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (83349770444569 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (459397262129 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_22 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (83315200839731 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296990266019 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨22, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (83315200839731 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296990266019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_23 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (41640327798037 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296994295793 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨23, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (41640327798037 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2296994295793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_24 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (41623067340287 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (91879931501 / 4000000000000 : ℝ))
      (E := (cell12351 ⟨24, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (41623067340287 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (91879931501 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_25 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (83211638060379 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (287125280633 / 12500000000000 : ℝ))
      (E := (cell12351 ⟨25, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (83211638060379 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (287125280633 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_26 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (41588582851403 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (287125786099 / 12500000000000 : ℝ))
      (E := (cell12351 ⟨26, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (41588582851403 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (287125786099 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_27 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (83142717575337 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297010247009 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨27, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (83142717575337 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297010247009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_28 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (41554146822813 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297014239649 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨28, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (41554146822813 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297014239649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_29 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (83073893881489 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (459403653939 / 20000000000000 : ℝ))
      (E := (cell12351 ⟨29, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (83073893881489 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (459403653939 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_30 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (20759879562727 / 25000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148511140709 / 50000000000000 : ℝ))
      (E := (cell12351 ⟨30, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (20759879562727 / 25000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148511140709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_31 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (8300516672203 / 10000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (143564142329 / 6250000000000 : ℝ))
      (E := (cell12351 ⟨31, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (8300516672203 / 10000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (143564142329 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_32 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (16594167852633 / 20000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (45940605189 / 2000000000000 : ℝ))
      (E := (cell12351 ⟨32, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (16594167852633 / 20000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (45940605189 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_33 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (41468267921391 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (459406845993 / 20000000000000 : ℝ))
      (E := (cell12351 ⟨33, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (41468267921391 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (459406845993 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_34 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (82902256429513 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297038249137 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨34, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (82902256429513 / 100000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297038249137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_35 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (10358500124019 / 12500000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297042259971 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨35, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (10358500124019 / 12500000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297042259971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_36 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (80892353027 / 97656250000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148523102577 / 50000000000000 : ℝ))
      (E := (cell12351 ⟨36, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (80892353027 / 97656250000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148523102577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_37 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (8279956192111 / 10000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (71782818843 / 3125000000000 : ℝ))
      (E := (cell12351 ⟨37, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (8279956192111 / 10000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (71782818843 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_38 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (16553075645161 / 20000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297054254359 / 100000000000000 : ℝ))
      (E := (cell12351 ⟨38, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (16553075645161 / 20000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (2297054254359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12351_39 : CellCertificate 12351 (179341009097479 / 2000000000000000 : ℝ) (170064155510909 / 100000000000000000 : ℝ) (343760048999651 / 10000000000000000 : ℝ)
    (cell12351 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · norm_num [cell12351]
  · have h := gap_lower (n := 12351) (a := (41365609191577 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148529121313 / 50000000000000 : ℝ))
      (E := (cell12351 ⟨39, by decide⟩).energy) (xi := (343760048999651 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12351 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12351]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12351])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12351) (a := (41365609191577 / 50000000000000 : ℝ)) (b := (41707739189 / 25000000000000 : ℝ)) (q := (1148529121313 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12351])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12351]

theorem cert12352_20 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (83384355041319 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296842839711 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨20, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (83384355041319 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296842839711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_21 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (10418720170869 / 12500000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (459369360173 / 20000000000000 : ℝ))
      (E := (cell12352 ⟨21, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (10418720170869 / 12500000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (459369360173 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_22 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (10414399010813 / 12500000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148425387243 / 50000000000000 : ℝ))
      (E := (cell12352 ⟨22, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (10414399010813 / 12500000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148425387243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_23 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (1301260111981 / 1562500000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296854823283 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨23, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (1301260111981 / 1562500000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296854823283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_24 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (5202882910923 / 6250000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (91874351059 / 4000000000000 : ℝ))
      (E := (cell12352 ⟨24, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (5202882910923 / 6250000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (91874351059 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_25 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (16642326055521 / 20000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296862812923 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨25, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (16642326055521 / 20000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296862812923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_26 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (83177158242613 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296866761229 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨26, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (83177158242613 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296866761229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_27 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (83142710437277 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296870799921 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨27, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (83142710437277 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296870799921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_28 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (1298566981707 / 1562500000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (574218689249 / 25000000000000 : ℝ))
      (E := (cell12352 ⟨28, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (1298566981707 / 1562500000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (574218689249 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_29 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (16614777477269 / 20000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (11484393761 / 500000000000 : ℝ))
      (E := (cell12352 ⟨29, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (16614777477269 / 20000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (11484393761 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_30 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (10379939009569 / 12500000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (57422069707 / 2500000000000 : ℝ))
      (E := (cell12352 ⟨30, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (10379939009569 / 12500000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (57422069707 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_31 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (5187822554251 / 6250000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296886750751 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨31, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (5187822554251 / 6250000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296886750751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_32 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (16594166745809 / 20000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296890758809 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨32, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (16594166745809 / 20000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296890758809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_33 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (82936530628113 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296894755961 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨33, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (82936530628113 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296894755961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_34 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (20725562883463 / 25000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148449371983 / 50000000000000 : ℝ))
      (E := (cell12352 ⟨34, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (20725562883463 / 25000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148449371983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_35 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (16573599283011 / 20000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296902724351 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨35, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (16573599283011 / 20000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296902724351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_36 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (82833765240673 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (28711334463 / 1250000000000 : ℝ))
      (E := (cell12352 ⟨36, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (82833765240673 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (28711334463 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_37 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (10349944747477 / 12500000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148455362947 / 50000000000000 : ℝ))
      (E := (cell12352 ⟨37, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (10349944747477 / 12500000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (1148455362947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_38 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (82765374601751 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (574228687257 / 25000000000000 : ℝ))
      (E := (cell12352 ⟨38, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (82765374601751 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (574228687257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12352_39 : CellCertificate 12352 (28021111664477 / 312500000000000 : ℝ) (340100765418509 / 200000000000000000 : ℝ) (8593287261947 / 250000000000000 : ℝ)
    (cell12352 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · norm_num [cell12352]
  · have h := gap_lower (n := 12352) (a := (82731215075901 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296918709759 / 100000000000000 : ℝ))
      (E := (cell12352 ⟨39, by decide⟩).energy) (xi := (8593287261947 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12352 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12352]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12352])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12352) (a := (82731215075901 / 100000000000000 : ℝ)) (b := (8340863683 / 5000000000000 : ℝ)) (q := (2296918709759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12352])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12352]

theorem cert12353_20 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (83384345640627 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148351712299 / 50000000000000 : ℝ))
      (E := (cell12353 ⟨20, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (83384345640627 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148351712299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_21 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (83349752291063 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296707403311 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨21, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (83349752291063 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296707403311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_22 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (16663036666993 / 20000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (574177848817 / 25000000000000 : ℝ))
      (E := (cell12353 ⟨22, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (16663036666993 / 20000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (574177848817 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_23 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (83280638739141 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296715404863 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨23, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (83280638739141 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296715404863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_24 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (10405764808821 / 12500000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296719377919 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨24, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (10405764808821 / 12500000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296719377919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_25 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (41605811248199 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296723376641 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨25, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (41605811248199 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296723376641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_26 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (83177150783947 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296727346333 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨26, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (83177150783947 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296727346333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_27 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (41571351650351 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148365674389 / 50000000000000 : ℝ))
      (E := (cell12353 ⟨27, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (41571351650351 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148365674389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_28 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (20777070003579 / 25000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (574183846797 / 25000000000000 : ℝ))
      (E := (cell12353 ⟨28, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (20777070003579 / 25000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (574183846797 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_29 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (1298029388947 / 1562500000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296739347637 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨29, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (1298029388947 / 1562500000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296739347637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_30 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (41519752951781 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (459348669937 / 20000000000000 : ℝ))
      (E := (cell12353 ⟨30, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (41519752951781 / 50000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (459348669937 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_31 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (83005155015327 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296747337347 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨31, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (83005155015327 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296747337347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_32 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (20742707049053 / 25000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (574187842841 / 25000000000000 : ℝ))
      (E := (cell12353 ⟨32, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (20742707049053 / 25000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (574187842841 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_33 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (82936525414691 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148377668347 / 50000000000000 : ℝ))
      (E := (cell12353 ⟨33, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (82936525414691 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148377668347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_34 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (82902246639397 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296759352167 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨34, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (82902246639397 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296759352167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_35 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (20716997959781 / 25000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296763360787 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨35, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (20716997959781 / 25000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296763360787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_36 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (3313350439313 / 4000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296767305237 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨36, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (3313350439313 / 4000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296767305237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_37 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (82799554039609 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (17943525811 / 781250000000 : ℝ))
      (E := (cell12353 ⟨37, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (82799554039609 / 100000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (17943525811 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_38 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (16553074195749 / 20000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148387649377 / 50000000000000 : ℝ))
      (E := (cell12353 ⟨38, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (16553074195749 / 20000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (1148387649377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12353_39 : CellCertificate 12353 (896646105633391 / 10000000000000000 : ℝ) (1700366121382251 / 1000000000000000000 : ℝ) (343702936807767 / 10000000000000000 : ℝ)
    (cell12353 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · norm_num [cell12353]
  · have h := gap_lower (n := 12353) (a := (16546242353931 / 20000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296779349393 / 100000000000000 : ℝ))
      (E := (cell12353 ⟨39, by decide⟩).energy) (xi := (343702936807767 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12353 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12353]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12353])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12353) (a := (16546242353931 / 20000000000000 : ℝ)) (b := (33360718567 / 20000000000000 : ℝ)) (q := (2296779349393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12353])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12353]

theorem cert12354_20 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (83384336241703 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148282031691 / 50000000000000 : ℝ))
      (E := (cell12354 ⟨20, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (83384336241703 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148282031691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_21 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (41674871608451 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296568059721 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨21, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (41674871608451 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296568059721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_22 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (83315174585113 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (574143002947 / 25000000000000 : ℝ))
      (E := (cell12354 ⟨22, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (83315174585113 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (574143002947 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_23 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (10410078789143 / 12500000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296576040537 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨23, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (10410078789143 / 12500000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296576040537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_24 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (3329844414719 / 4000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296580033519 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨24, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (3329844414719 / 4000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296580033519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_25 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (20802903679189 / 25000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (287072999323 / 12500000000000 : ℝ))
      (E := (cell12354 ⟨25, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (20802903679189 / 25000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (287072999323 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_26 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (83177143326807 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296588044109 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨26, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (83177143326807 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296588044109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_27 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (83142696165613 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296592010393 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨27, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (83142696165613 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296592010393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_28 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (83108273200829 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296596013367 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨28, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (83108273200829 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296596013367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_29 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (20768468600069 / 25000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (574149999389 / 25000000000000 : ℝ))
      (E := (cell12354 ⟨29, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (20768468600069 / 25000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (574149999389 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_30 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (83039499731937 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (459320804823 / 20000000000000 : ℝ))
      (E := (cell12354 ⟨30, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (83039499731937 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (459320804823 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_31 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (83005149163963 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (459321595711 / 20000000000000 : ℝ))
      (E := (cell12354 ⟨31, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (83005149163963 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (459321595711 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_32 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (10371352833083 / 12500000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (229661198007 / 10000000000000 : ℝ))
      (E := (cell12354 ⟨32, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (10371352833083 / 12500000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (229661198007 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_33 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (41468260101257 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296615972167 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨33, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (41468260101257 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296615972167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_34 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (20725560436537 / 25000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296620015173 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨34, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (20725560436537 / 25000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296620015173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_35 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (2071699681609 / 2500000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (287077999187 / 12500000000000 : ℝ))
      (E := (cell12354 ⟨35, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (2071699681609 / 2500000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (287077999187 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_36 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (82833756726103 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296627966987 / 100000000000000 : ℝ))
      (E := (cell12354 ⟨36, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (82833756726103 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (2296627966987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_37 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (82799550100489 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (14353949971 / 625000000000 : ℝ))
      (E := (cell12354 ⟨37, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (82799550100489 / 100000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (14353949971 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_38 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (16553073471357 / 20000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (71769873819 / 3125000000000 : ℝ))
      (E := (cell12354 ⟨38, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (16553073471357 / 20000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (71769873819 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12354_39 : CellCertificate 12354 (112077080324581 / 1250000000000000 : ℝ) (1700228437972789 / 1000000000000000000 : ℝ) (13746975519517 / 400000000000000 : ℝ)
    (cell12354 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · norm_num [cell12354]
  · have h := gap_lower (n := 12354) (a := (41365604232209 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148319992731 / 50000000000000 : ℝ))
      (E := (cell12354 ⟨39, by decide⟩).energy) (xi := (13746975519517 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12354 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12354]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12354])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12354) (a := (41365604232209 / 50000000000000 : ℝ)) (b := (166789914279 / 100000000000000 : ℝ)) (q := (1148319992731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12354])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12354]

theorem cert12355_20 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (41692163422273 / 50000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148212378033 / 50000000000000 : ℝ))
      (E := (cell12355 ⟨20, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (41692163422273 / 50000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148212378033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_21 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (83349734144469 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296428770093 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨21, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (83349734144469 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296428770093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_22 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (20828791459237 / 25000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296432740627 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨22, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (20828791459237 / 25000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296432740627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_23 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (41640310944397 / 50000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (35881823911 / 1562500000000 : ℝ))
      (E := (cell12355 ⟨23, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (41640310944397 / 50000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (35881823911 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_24 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (20811525566747 / 25000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296440743279 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨24, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (20811525566747 / 25000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296440743279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_25 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (83211606938681 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296444725109 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨25, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (83211606938681 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296444725109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_26 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (10397141983899 / 12500000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (229644873779 / 10000000000000 : ℝ))
      (E := (cell12355 ⟨26, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (10397141983899 / 12500000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (229644873779 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_27 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (83142689032009 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296452726361 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨27, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (83142689032009 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296452726361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_28 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (20777066597197 / 25000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148228376197 / 50000000000000 : ℝ))
      (E := (cell12355 ⟨28, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (20777066597197 / 25000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148228376197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_29 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (83073867909349 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148230350979 / 50000000000000 : ℝ))
      (E := (cell12355 ⟨29, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (83073867909349 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148230350979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_30 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (41519746780839 / 50000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296464694613 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨30, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (41519746780839 / 50000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296464694613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_31 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (20751285828481 / 25000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (574117183219 / 25000000000000 : ℝ))
      (E := (cell12355 ⟨31, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (20751285828481 / 25000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (574117183219 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_32 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (82970817134401 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148236350989 / 50000000000000 : ℝ))
      (E := (cell12355 ⟨32, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (82970817134401 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148236350989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_33 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (82936514991583 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296476720929 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨33, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (82936514991583 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296476720929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_34 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (10362779606763 / 12500000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (459296146597 / 20000000000000 : ℝ))
      (E := (cell12355 ⟨34, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (10362779606763 / 12500000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (459296146597 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_35 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (82867982690761 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (574121170269 / 25000000000000 : ℝ))
      (E := (cell12355 ⟨35, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (82867982690761 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (574121170269 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_36 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (82833752470507 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (229648868367 / 10000000000000 : ℝ))
      (E := (cell12355 ⟨36, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (82833752470507 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (229648868367 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_37 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (16559909232491 / 20000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296492683269 / 100000000000000 : ℝ))
      (E := (cell12355 ⟨37, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (16559909232491 / 20000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (2296492683269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_38 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (82765363735873 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (574124170181 / 25000000000000 : ℝ))
      (E := (cell12355 ⟨38, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (82765363735873 / 100000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (574124170181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12355_39 : CellCertificate 12355 (896587184151913 / 10000000000000000 : ℝ) (1700090776858743 / 1000000000000000000 : ℝ) (171822922008483 / 5000000000000000 : ℝ)
    (cell12355 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · norm_num [cell12355]
  · have h := gap_lower (n := 12355) (a := (20682801290047 / 25000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148250338329 / 50000000000000 : ℝ))
      (E := (cell12355 ⟨39, by decide⟩).energy) (xi := (171822922008483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12355 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12355]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12355])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12355) (a := (20682801290047 / 25000000000000 : ℝ)) (b := (20847029749 / 12500000000000 : ℝ)) (q := (1148250338329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12355])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12355]

theorem cert12356_20 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (41692158724579 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296285560891 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨20, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (41692158724579 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296285560891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_21 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (41674862536881 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296289534431 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨21, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (41674862536881 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296289534431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_22 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (83315157090469 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (287036690437 / 12500000000000 : ℝ))
      (E := (cell12356 ⟨22, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (83315157090469 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (287036690437 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_23 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (83280613466091 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148148766239 / 50000000000000 : ℝ))
      (E := (cell12356 ⟨23, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (83280613466091 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148148766239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_24 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (83246094167607 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296301507197 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨24, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (83246094167607 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296301507197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_25 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (8321159916217 / 10000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296305509859 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨25, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (8321159916217 / 10000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296305509859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_26 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (41588564208551 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (143519346509 / 6250000000000 : ℝ))
      (E := (cell12356 ⟨26, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (41588564208551 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (143519346509 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_27 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (8314268189989 / 10000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (574078374171 / 25000000000000 : ℝ))
      (E := (cell12356 ⟨27, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (8314268189989 / 10000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (574078374171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_28 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (83108259578191 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296317487409 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨28, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (83108259578191 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296317487409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_29 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (41536930709913 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148160759649 / 50000000000000 : ℝ))
      (E := (cell12356 ⟨29, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (41536930709913 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148160759649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_30 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (83039487392783 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148162739069 / 50000000000000 : ℝ))
      (E := (cell12356 ⟨30, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (83039487392783 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148162739069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_31 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (83005137465211 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148164741653 / 50000000000000 : ℝ))
      (E := (cell12356 ⟨31, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (83005137465211 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148164741653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_32 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (82970811605423 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148166739281 / 50000000000000 : ℝ))
      (E := (cell12356 ⟨32, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (82970811605423 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148166739281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_33 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (10367063722737 / 12500000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (574084366471 / 25000000000000 : ℝ))
      (E := (cell12356 ⟨33, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (10367063722737 / 12500000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (574084366471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_34 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (41451115981633 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296341505601 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨34, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (41451115981633 / 50000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296341505601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_35 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (10358497264791 / 12500000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296345482119 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨35, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (10358497264791 / 12500000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296345482119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_36 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (82833748216037 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296349455287 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨36, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (82833748216037 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296349455287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_37 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (82799542225507 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148176742409 / 50000000000000 : ℝ))
      (E := (cell12356 ⟨37, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (82799542225507 / 100000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (1148176742409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_38 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (10345670014501 / 12500000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296357454301 / 100000000000000 : ℝ))
      (E := (cell12356 ⟨38, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (10345670014501 / 12500000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (2296357454301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12356_39 : CellCertificate 12356 (896557730298059 / 10000000000000000 : ℝ) (1699953138034697 / 1000000000000000000 : ℝ) (5369020388961 / 156250000000000 : ℝ)
    (cell12356 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · norm_num [cell12356]
  · have h := gap_lower (n := 12356) (a := (16546240371393 / 20000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (229636148167 / 10000000000000 : ℝ))
      (E := (cell12356 ⟨39, by decide⟩).energy) (xi := (5369020388961 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12356 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12356]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12356])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12356) (a := (16546240371393 / 20000000000000 : ℝ)) (b := (83381281987 / 50000000000000 : ℝ)) (q := (229636148167 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12356])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12356]

theorem cert12357_20 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (5211519253471 / 6250000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148073209809 / 50000000000000 : ℝ))
      (E := (cell12357 ⟨20, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (5211519253471 / 6250000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148073209809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_21 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (41674858002391 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296150411001 / 100000000000000 : ℝ))
      (E := (cell12357 ⟨21, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (41674858002391 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296150411001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_22 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (83315148345677 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (459230872079 / 20000000000000 : ℝ))
      (E := (cell12357 ⟨22, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (83315148345677 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (459230872079 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_23 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (10410075630629 / 12500000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1836926711 / 80000000000 : ℝ))
      (E := (cell12357 ⟨23, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (10410075630629 / 12500000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1836926711 / 80000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_24 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (83246086069831 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148081191807 / 50000000000000 : ℝ))
      (E := (cell12357 ⟨24, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (83246086069831 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148081191807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_25 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (3328463655489 / 4000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (459233269767 / 20000000000000 : ℝ))
      (E := (cell12357 ⟨25, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (3328463655489 / 4000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (459233269767 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_26 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (83177120964537 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (459234069281 / 20000000000000 : ℝ))
      (E := (cell12357 ⟨26, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (83177120964537 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (459234069281 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_27 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (10392834346157 / 12500000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296174379769 / 100000000000000 : ℝ))
      (E := (cell12357 ⟨27, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (10392834346157 / 12500000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296174379769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_28 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (83108252769039 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (91847133411 / 4000000000000 : ℝ))
      (E := (cell12357 ⟨28, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (83108252769039 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (91847133411 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_29 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (20768463732927 / 25000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (574045583167 / 25000000000000 : ℝ))
      (E := (cell12357 ⟨29, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (20768463732927 / 25000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (574045583167 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_30 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (20759870306313 / 25000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296186374691 / 100000000000000 : ℝ))
      (E := (cell12357 ⟨30, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (20759870306313 / 25000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296186374691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_31 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (83005131617821 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148095173427 / 50000000000000 : ℝ))
      (E := (cell12357 ⟨31, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (83005131617821 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148095173427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_32 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (8297080607773 / 10000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296194368349 / 100000000000000 : ℝ))
      (E := (cell12357 ⟨32, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (8297080607773 / 10000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296194368349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_33 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (16587300914691 / 20000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (229619832413 / 10000000000000 : ℝ))
      (E := (cell12357 ⟨33, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (16587300914691 / 20000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (229619832413 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_34 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (2590694596051 / 3125000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148101166513 / 50000000000000 : ℝ))
      (E := (cell12357 ⟨34, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (2590694596051 / 3125000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148101166513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_35 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (4143398677353 / 5000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (459241267607 / 20000000000000 : ℝ))
      (E := (cell12357 ⟨35, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (4143398677353 / 5000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (459241267607 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_36 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (82833743962693 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148105170229 / 50000000000000 : ℝ))
      (E := (cell12357 ⟨36, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (82833743962693 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (1148105170229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_37 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (41399769144823 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296214341367 / 100000000000000 : ℝ))
      (E := (cell12357 ⟨37, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (41399769144823 / 50000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296214341367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_38 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (82765356497189 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296218341609 / 100000000000000 : ℝ))
      (E := (cell12357 ⟨38, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (82765356497189 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (2296218341609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12357_39 : CellCertificate 12357 (224132070258491 / 2500000000000000 : ℝ) (849907760747619 / 500000000000000000 : ℝ) (42948596327019 / 1250000000000000 : ℝ)
    (cell12357 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · norm_num [cell12357]
  · have h := gap_lower (n := 12357) (a := (82731198554749 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (229622234181 / 10000000000000 : ℝ))
      (E := (cell12357 ⟨39, by decide⟩).energy) (xi := (42948596327019 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12357 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12357]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12357])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12357) (a := (82731198554749 / 100000000000000 : ℝ)) (b := (2605451441 / 1562500000000 : ℝ)) (q := (229622234181 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12357])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12357]

theorem cert12358_20 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (83384298663681 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148003666123 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨20, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (83384298663681 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148003666123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_21 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (10418713367191 / 12500000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296011283271 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨21, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (10418713367191 / 12500000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296011283271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_22 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (8331513960257 / 10000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296015309617 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨22, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (8331513960257 / 10000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296015309617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_23 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (83280596625619 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148009649559 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨23, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (83280596625619 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148009649559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_24 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (83246077973659 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148011657097 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨24, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (83246077973659 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148011657097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_25 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (20802895903461 / 25000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296027300399 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨25, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (20802895903461 / 25000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296027300399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_26 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (10397139189187 / 12500000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148015630671 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨26, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (10397139189187 / 12500000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148015630671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_27 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (16628533528021 / 20000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (459207051761 / 20000000000000 : ℝ))
      (E := (cell12358 ⟨27, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (16628533528021 / 20000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (459207051761 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_28 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (8310824596133 / 10000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148019647997 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨28, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (8310824596133 / 10000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148019647997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_29 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (41536924222497 / 50000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148021629489 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨29, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (41536924222497 / 50000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148021629489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_30 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (16607895011817 / 20000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (574011816829 / 25000000000000 : ℝ))
      (E := (cell12358 ⟨30, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (16607895011817 / 20000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (574011816829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_31 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (20751281442939 / 25000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (287006408127 / 12500000000000 : ℝ))
      (E := (cell12358 ⟨31, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (20751281442939 / 25000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (287006408127 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_32 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (82970800551321 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (229605525429 / 10000000000000 : ℝ))
      (E := (cell12358 ⟨32, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (82970800551321 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (229605525429 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_33 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (82936499366257 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296059237121 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨33, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (82936499366257 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296059237121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_34 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (20725555546301 / 25000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296063273829 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨34, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (20725555546301 / 25000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296063273829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_35 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (82867968976957 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296067248823 / 100000000000000 : ℝ))
      (E := (cell12358 ⟨35, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (82867968976957 / 100000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (2296067248823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_36 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (41416869855237 / 50000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148035640283 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨36, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (41416869855237 / 50000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148035640283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_37 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (8279953435487 / 10000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (574018813229 / 25000000000000 : ℝ))
      (E := (cell12358 ⟨37, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (8279953435487 / 10000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (574018813229 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_38 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (10345669109927 / 12500000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (574019806329 / 25000000000000 : ℝ))
      (E := (cell12358 ⟨38, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (10345669109927 / 12500000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (574019806329 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12358_39 : CellCertificate 12358 (112062354544813 / 1250000000000000 : ℝ) (849838963617477 / 500000000000000000 : ℝ) (171780120591763 / 5000000000000000 : ℝ)
    (cell12358 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · norm_num [cell12358]
  · have h := gap_lower (n := 12358) (a := (4136559762677 / 5000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148041628539 / 50000000000000 : ℝ))
      (E := (cell12358 ⟨39, by decide⟩).energy) (xi := (171780120591763 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12358 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12358]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12358])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12358) (a := (4136559762677 / 5000000000000 : ℝ)) (b := (83367611371 / 50000000000000 : ℝ)) (q := (1148041628539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12358])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12358]

theorem cert12359_20 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (83384289273591 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295868298781 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨20, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (83384289273591 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295868298781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_21 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (83349697871999 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295872267779 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨21, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (83349697871999 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295872267779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_22 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (83315130861147 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (18367010503 / 800000000000 : ℝ))
      (E := (cell12359 ⟨22, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (83315130861147 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (18367010503 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_23 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (1665611764157 / 2000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295880263587 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨23, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (1665611764157 / 2000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295880263587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_24 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (20811517469773 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147942149469 / 50000000000000 : ℝ))
      (E := (cell12359 ⟨24, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (20811517469773 / 25000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147942149469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_25 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (83211575842027 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (286986030979 / 12500000000000 : ℝ))
      (E := (cell12359 ⟨25, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (83211575842027 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (286986030979 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_26 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (83177106063979 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147946144479 / 50000000000000 : ℝ))
      (E := (cell12359 ⟨26, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (83177106063979 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147946144479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_27 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (83142660512439 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (459179250121 / 20000000000000 : ℝ))
      (E := (cell12359 ⟨27, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (83142660512439 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (459179250121 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_28 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (16621647831013 / 20000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147950126353 / 50000000000000 : ℝ))
      (E := (cell12359 ⟨28, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (16621647831013 / 20000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147950126353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_29 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (83073841959683 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147952119889 / 50000000000000 : ℝ))
      (E := (cell12359 ⟨29, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (83073841959683 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147952119889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_30 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (41519734447141 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295908272971 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨30, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (41519734447141 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295908272971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_31 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (41502559963507 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (459182447559 / 20000000000000 : ℝ))
      (E := (cell12359 ⟨31, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (41502559963507 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (459182447559 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_32 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (16594159005239 / 20000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1793684573 / 78125000000 : ℝ))
      (E := (cell12359 ⟨32, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (16594159005239 / 20000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1793684573 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_33 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (5183530885019 / 6250000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (459184052681 / 20000000000000 : ℝ))
      (E := (cell12359 ⟨33, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (5183530885019 / 6250000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (459184052681 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_34 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (82902217297979 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (459184853889 / 20000000000000 : ℝ))
      (E := (cell12359 ⟨34, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (82902217297979 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (459184853889 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_35 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (41433982204009 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295928214487 / 100000000000000 : ℝ))
      (E := (cell12359 ⟨35, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (41433982204009 / 50000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (2295928214487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_36 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (4141686772969 / 5000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (459186443399 / 20000000000000 : ℝ))
      (E := (cell12359 ⟨36, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (4141686772969 / 5000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (459186443399 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_37 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (82799530421179 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (229593621947 / 10000000000000 : ℝ))
      (E := (cell12359 ⟨37, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (82799530421179 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (229593621947 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_38 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (82765349262689 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (573985055689 / 25000000000000 : ℝ))
      (E := (cell12359 ⟨38, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (82765349262689 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (573985055689 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12359_39 : CellCertificate 12359 (448234698135277 / 5000000000000000 : ℝ) (424885088812109 / 250000000000000000 : ℝ) (343531716594241 / 10000000000000000 : ℝ)
    (cell12359 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · norm_num [cell12359]
  · have h := gap_lower (n := 12359) (a := (82731191953337 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147972113739 / 50000000000000 : ℝ))
      (E := (cell12359 ⟨39, by decide⟩).energy) (xi := (343531716594241 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12359 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12359]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12359])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12359) (a := (82731191953337 / 100000000000000 : ℝ)) (b := (83360777763 / 50000000000000 : ℝ)) (q := (1147972113739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12359])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12359]

theorem cert12360_20 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (20846069971317 / 25000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147864688731 / 50000000000000 : ℝ))
      (E := (cell12360 ⟨20, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (20846069971317 / 25000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147864688731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_21 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (16669937761639 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295733364523 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨21, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (16669937761639 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295733364523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_22 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (8331512212141 / 10000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (573934327969 / 25000000000000 : ℝ))
      (E := (cell12360 ⟨22, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (8331512212141 / 10000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (573934327969 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_23 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (41640289895863 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295741340469 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨23, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (41640289895863 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295741340469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_24 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (83246061786129 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295745337847 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨24, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (83246061786129 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295745337847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_25 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (41605784035887 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (459149861571 / 20000000000000 : ℝ))
      (E := (cell12360 ⟨25, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (41605784035887 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (459149861571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_26 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (16635419723197 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (573938328121 / 25000000000000 : ℝ))
      (E := (cell12360 ⟨26, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (16635419723197 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (573938328121 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_27 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (16628530677251 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295757296767 / 100000000000000 : ℝ))
      (E := (cell12360 ⟨27, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (16628530677251 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (2295757296767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_28 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (20777058087561 / 25000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (71742541321 / 3125000000000 : ℝ))
      (E := (cell12360 ⟨28, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (20777058087561 / 25000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (71742541321 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_29 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (1298028679309 / 1562500000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (28697066669 / 1250000000000 : ℝ))
      (E := (cell12360 ⟨29, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (1298028679309 / 1562500000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (28697066669 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_30 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (41519731365421 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (114788466659 / 5000000000000 : ℝ))
      (E := (cell12360 ⟨30, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (41519731365421 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (114788466659 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_31 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (16601022816719 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (459154664739 / 20000000000000 : ℝ))
      (E := (cell12360 ⟨31, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (16601022816719 / 20000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (459154664739 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_32 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (82970789502353 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (229577730727 / 10000000000000 : ℝ))
      (E := (cell12360 ⟨32, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (82970789502353 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (229577730727 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_33 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (41468244477797 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (280246739 / 12207031250 : ℝ))
      (E := (cell12360 ⟨33, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (41468244477797 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (280246739 / 12207031250 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_34 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (41451106205979 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (229578531987 / 10000000000000 : ℝ))
      (E := (cell12360 ⟨34, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (41451106205979 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (229578531987 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_35 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (20716989960061 / 25000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (114789464681 / 5000000000000 : ℝ))
      (E := (cell12360 ⟨35, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (20716989960061 / 25000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (114789464681 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_36 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (8283373120941 / 10000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147896633491 / 50000000000000 : ℝ))
      (E := (cell12360 ⟨36, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (8283373120941 / 10000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (1147896633491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_37 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (41399763244287 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (573949324917 / 25000000000000 : ℝ))
      (E := (cell12360 ⟨37, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (41399763244287 / 50000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (573949324917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_38 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (82765345647007 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (17935947463 / 781250000000 : ℝ))
      (E := (cell12360 ⟨38, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (82765345647007 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (17935947463 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12360_39 : CellCertificate 12360 (896439960768993 / 10000000000000000 : ℝ) (424850701382569 / 250000000000000000 : ℝ) (343503196846913 / 10000000000000000 : ℝ)
    (cell12360 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · norm_num [cell12360]
  · have h := gap_lower (n := 12360) (a := (82731188654141 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (143487828313 / 6250000000000 : ℝ))
      (E := (cell12360 ⟨39, by decide⟩).energy) (xi := (343503196846913 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12360 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12360]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12360])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12360) (a := (82731188654141 / 100000000000000 : ℝ)) (b := (166707890577 / 100000000000000 : ℝ)) (q := (143487828313 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12360])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12360]

theorem cert12361_20 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (83384270498709 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295590451809 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨20, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (83384270498709 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295590451809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_21 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (20837419936529 / 25000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295594456973 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨21, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (20837419936529 / 25000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295594456973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_22 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (83315113383357 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (286949810187 / 12500000000000 : ℝ))
      (E := (cell12361 ⟨22, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (83315113383357 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (286949810187 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_23 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (16656114275449 / 20000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (1147801235727 / 50000000000000 : ℝ))
      (E := (cell12361 ⟨23, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (16656114275449 / 20000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (1147801235727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_24 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (83246053694769 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (573901607731 / 25000000000000 : ℝ))
      (E := (cell12361 ⟨24, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (83246053694769 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (573901607731 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_25 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (83211560303083 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (71737825691 / 3125000000000 : ℝ))
      (E := (cell12361 ⟨25, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (83211560303083 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (71737825691 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_26 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (41588545584757 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295614448691 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨26, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (41588545584757 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295614448691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_27 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (16628529252311 / 20000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295618455697 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨27, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (16628529252311 / 20000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295618455697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_28 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (16621645109373 / 20000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (459124489253 / 20000000000000 : ℝ))
      (E := (cell12361 ⟨28, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (16621645109373 / 20000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (459124489253 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_29 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (83073828993271 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295626423299 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨29, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (83073828993271 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295626423299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_30 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (20759864142191 / 25000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (1147815223973 / 50000000000000 : ℝ))
      (E := (cell12361 ⟨30, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (20759864142191 / 25000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (1147815223973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_31 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (83005108241499 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (143477150357 / 6250000000000 : ℝ))
      (E := (cell12361 ⟨31, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (83005108241499 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (143477150357 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_32 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (41485391989897 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (1147819207893 / 50000000000000 : ℝ))
      (E := (cell12361 ⟨32, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (41485391989897 / 50000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (1147819207893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_33 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (82936483752127 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295642421669 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨33, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (82936483752127 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295642421669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_34 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (4145110376357 / 5000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (229564642511 / 10000000000000 : ℝ))
      (E := (cell12361 ⟨34, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (4145110376357 / 5000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (229564642511 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_35 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (82867955273633 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295650427631 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨35, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (82867955273633 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295650427631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_36 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (16566745392113 / 20000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295654430529 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨36, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (16566745392113 / 20000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295654430529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_37 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (82799522557053 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (229565837623 / 10000000000000 : ℝ))
      (E := (cell12361 ⟨37, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (82799522557053 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (229565837623 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_38 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (82765342032371 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295662382841 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨38, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (82765342032371 / 100000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295662382841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12361_39 : CellCertificate 12361 (896410529852697 / 10000000000000000 : ℝ) (1699265278075067 / 1000000000000000000 : ℝ) (171737340970079 / 5000000000000000 : ℝ)
    (cell12361 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · norm_num [cell12361]
  · have h := gap_lower (n := 12361) (a := (1654623707119 / 2000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295666392363 / 100000000000000 : ℝ))
      (E := (cell12361 ⟨39, by decide⟩).energy) (xi := (171737340970079 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12361 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12361]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12361])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12361) (a := (1654623707119 / 2000000000000 : ℝ)) (b := (166694227893 / 100000000000000 : ℝ)) (q := (2295666392363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12361])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12361]

theorem cert12362_20 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (20846065278479 / 25000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (459090327661 / 20000000000000 : ℝ))
      (E := (cell12362 ⟨20, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (20846065278479 / 25000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (459090327661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_21 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (41674835342881 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147727830831 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨21, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (41674835342881 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147727830831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_22 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (83315104646987 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (143466227929 / 6250000000000 : ℝ))
      (E := (cell12362 ⟨22, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (83315104646987 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (143466227929 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_23 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (10410070370551 / 12500000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147731828271 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨23, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (10410070370551 / 12500000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147731828271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_24 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (20811511401253 / 25000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147733818253 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨24, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (20811511401253 / 25000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147733818253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_25 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (20802888133989 / 25000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (7173348903 / 312500000000 : ℝ))
      (E := (cell12362 ⟨25, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (20802888133989 / 25000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (7173348903 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_26 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (41588541862283 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (573868909799 / 25000000000000 : ℝ))
      (E := (cell12362 ⟨26, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (41588541862283 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (573868909799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_27 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (2598207473073 / 3125000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147739805291 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨27, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (2598207473073 / 3125000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147739805291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_28 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (2597131835779 / 3125000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (459096724937 / 20000000000000 : ℝ))
      (E := (cell12362 ⟨28, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (2597131835779 / 3125000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (459096724937 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_29 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (83073822512169 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295487626023 / 100000000000000 : ℝ))
      (E := (cell12362 ⟨29, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (83073822512169 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295487626023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_30 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (83039450408049 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147745808633 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨30, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (83039450408049 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147745808633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_31 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (41502551200363 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295495600851 / 100000000000000 : ℝ))
      (E := (cell12362 ⟨31, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (41502551200363 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295495600851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_32 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (82970778458517 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147749789493 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨32, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (82970778458517 / 100000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147749789493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_33 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (5183529909369 / 6250000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295503612197 / 100000000000000 : ℝ))
      (E := (cell12362 ⟨33, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (5183529909369 / 6250000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295503612197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_34 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (41451101321763 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295507585161 / 100000000000000 : ℝ))
      (E := (cell12362 ⟨34, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (41451101321763 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295507585161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_35 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (41433975354093 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295511616519 / 100000000000000 : ℝ))
      (E := (cell12362 ⟨35, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (41433975354093 / 50000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (2295511616519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_36 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (20708430678211 / 25000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147757795199 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨36, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (20708430678211 / 25000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147757795199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_37 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (10349939828327 / 12500000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (57387989161 / 2500000000000 : ℝ))
      (E := (cell12362 ⟨37, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (10349939828327 / 12500000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (57387989161 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_38 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (4138266920939 / 5000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147761802077 / 50000000000000 : ℝ))
      (E := (cell12362 ⟨38, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (4138266920939 / 5000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (1147761802077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12362_39 : CellCertificate 12362 (179276220704109 / 2000000000000000 : ℝ) (424781943219351 / 250000000000000000 : ℝ) (85861542968149 / 2500000000000000 : ℝ)
    (cell12362 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · norm_num [cell12362]
  · have h := gap_lower (n := 12362) (a := (20682795514691 / 25000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (573881896713 / 25000000000000 : ℝ))
      (E := (cell12362 ⟨39, by decide⟩).energy) (xi := (85861542968149 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12362 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12362]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12362])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12362) (a := (20682795514691 / 25000000000000 : ℝ)) (b := (6667222699 / 4000000000000 : ℝ)) (q := (573881896713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12362])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12362]

theorem cert12363_20 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (41692125865443 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (286914109839 / 12500000000000 : ℝ))
      (E := (cell12363 ⟨20, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (41692125865443 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (286914109839 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_21 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (83349661627131 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295316920327 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨21, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (83349661627131 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295316920327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_22 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (83315095912301 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (71728777071 / 3125000000000 : ℝ))
      (E := (cell12363 ⟨22, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (83315095912301 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (71728777071 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_23 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (41640277276607 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147662447867 / 50000000000000 : ℝ))
      (E := (cell12363 ⟨23, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (41640277276607 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147662447867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_24 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (41623018758429 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147664448129 / 50000000000000 : ℝ))
      (E := (cell12363 ⟨24, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (41623018758429 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147664448129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_25 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (83211544770391 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295332871683 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨25, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (83211544770391 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295332871683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_26 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (4158853814057 / 5000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (573834221 / 25000000000 : ℝ))
      (E := (cell12363 ⟨26, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (4158853814057 / 5000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (573834221 / 25000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_27 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (415713160083 / 500000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295340878239 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨27, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (415713160083 / 500000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295340878239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_28 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (41554105972217 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295344857533 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨28, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (41554105972217 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295344857533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_29 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (20768454008117 / 25000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147674441621 / 50000000000000 : ℝ))
      (E := (cell12363 ⟨29, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (20768454008117 / 25000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147674441621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_30 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (10379930531087 / 12500000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (459070568229 / 20000000000000 : ℝ))
      (E := (cell12363 ⟨30, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (10379930531087 / 12500000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (459070568229 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_31 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (3320203862451 / 4000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (573839212653 / 25000000000000 : ℝ))
      (E := (cell12363 ⟨31, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (3320203862451 / 4000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (573839212653 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_32 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (82970772938523 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147680427699 / 50000000000000 : ℝ))
      (E := (cell12363 ⟨32, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (82970772938523 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147680427699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_33 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (41468236674461 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295364857479 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨33, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (41468236674461 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295364857479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_34 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (16580439552223 / 20000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295368858601 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨34, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (16580439552223 / 20000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295368858601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_35 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (41433973071951 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (17932600471 / 781250000000 : ℝ))
      (E := (cell12363 ⟨35, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (41433973071951 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (17932600471 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_36 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (41416859233123 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295376863831 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨36, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (41416859233123 / 50000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295376863831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_37 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (5174969668579 / 6250000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147690405829 / 50000000000000 : ℝ))
      (E := (cell12363 ⟨37, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (5174969668579 / 6250000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (1147690405829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_38 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (82765334806233 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295384821873 / 100000000000000 : ℝ))
      (E := (cell12363 ⟨38, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (82765334806233 / 100000000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (2295384821873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12363_39 : CellCertificate 12363 (179270336354283 / 2000000000000000 : ℝ) (339798057986377 / 200000000000000000 : ℝ) (343417666642843 / 10000000000000000 : ℝ)
    (cell12363 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · norm_num [cell12363]
  · have h := gap_lower (n := 12363) (a := (10341397345323 / 12500000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (573847209119 / 25000000000000 : ℝ))
      (E := (cell12363 ⟨39, by decide⟩).energy) (xi := (343417666642843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12363 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12363]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12363])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12363) (a := (10341397345323 / 12500000000000 : ℝ)) (b := (166666909321 / 100000000000000 : ℝ)) (q := (573847209119 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12363])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12363]

theorem cert12364_20 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (4169212117481 / 5000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573793557819 / 25000000000000 : ℝ))
      (E := (cell12364 ⟨20, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (4169212117481 / 5000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573793557819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_21 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (83349652570223 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295178232969 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨21, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (83349652570223 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295178232969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_22 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (41657543589649 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573795549503 / 25000000000000 : ℝ))
      (E := (cell12364 ⟨22, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (41657543589649 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573795549503 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_23 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (41640273071831 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (1147593094517 / 50000000000000 : ℝ))
      (E := (cell12364 ⟨23, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (41640273071831 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (1147593094517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_24 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (41623014715153 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295190210181 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨24, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (41623014715153 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295190210181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_25 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (20802884251597 / 25000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573798551751 / 25000000000000 : ℝ))
      (E := (cell12364 ⟨25, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (20802884251597 / 25000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573798551751 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_26 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (20794267209809 / 25000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (459039636621 / 20000000000000 : ℝ))
      (E := (cell12364 ⟨26, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (20794267209809 / 25000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (459039636621 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_27 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (41571312448173 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295202200261 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨27, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (41571312448173 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295202200261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_28 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (83108205145381 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573801550811 / 25000000000000 : ℝ))
      (E := (cell12364 ⟨28, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (83108205145381 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573801550811 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_29 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (83073809554169 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (459042038991 / 20000000000000 : ℝ))
      (E := (cell12364 ⟨29, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (83073809554169 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (459042038991 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_30 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (16607887618141 / 20000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295214178061 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨30, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (16607887618141 / 20000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295214178061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_31 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (41502545361573 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (1147609077499 / 50000000000000 : ℝ))
      (E := (cell12364 ⟨31, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (41502545361573 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (1147609077499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_32 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (82970767419811 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295222186499 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨32, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (82970767419811 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295222186499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_33 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (82936468149183 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (286903269689 / 12500000000000 : ℝ))
      (E := (cell12364 ⟨33, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (82936468149183 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (286903269689 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_34 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (41451096439953 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (459046025657 / 20000000000000 : ℝ))
      (E := (cell12364 ⟨34, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (41451096439953 / 50000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (459046025657 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_35 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (82867941580781 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295234158937 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨35, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (82867941580781 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295234158937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_36 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (82833714220771 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295238133591 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨36, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (82833714220771 / 100000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295238133591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_37 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (16559902153799 / 20000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295242170529 / 100000000000000 : ℝ))
      (E := (cell12364 ⟨37, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (16559902153799 / 20000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (2295242170529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_38 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (8276533119473 / 10000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573811538333 / 25000000000000 : ℝ))
      (E := (cell12364 ⟨38, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (8276533119473 / 10000000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (573811538333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12364_39 : CellCertificate 12364 (179264452920837 / 2000000000000000 : ℝ) (1698852829233109 / 1000000000000000000 : ℝ) (343389166249519 / 10000000000000000 : ℝ)
    (cell12364 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · norm_num [cell12364]
  · have h := gap_lower (n := 12364) (a := (5170698466713 / 6250000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (1147625070619 / 50000000000000 : ℝ))
      (E := (cell12364 ⟨39, by decide⟩).energy) (xi := (343389166249519 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12364 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12364]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12364])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12364) (a := (5170698466713 / 6250000000000 : ℝ)) (b := (16665325343 / 10000000000000 : ℝ)) (q := (1147625070619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12364])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12364]

theorem cert12365_20 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (41692116485059 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147517789753 / 50000000000000 : ℝ))
      (E := (cell12365 ⟨20, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (41692116485059 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147517789753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_21 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (41674821757519 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (573759899897 / 25000000000000 : ℝ))
      (E := (cell12365 ⟨21, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (41674821757519 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (573759899897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_22 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (83315078447977 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147521791897 / 50000000000000 : ℝ))
      (E := (cell12365 ⟨22, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (83315078447977 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147521791897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_23 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (83280537735753 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147523797377 / 50000000000000 : ℝ))
      (E := (cell12365 ⟨23, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (83280537735753 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147523797377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_24 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (20811505336339 / 25000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295051578277 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨24, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (20811505336339 / 25000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295051578277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_25 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (83211529243947 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295055596561 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨25, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (83211529243947 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295055596561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_26 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (83177061398853 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295059594897 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨26, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (83177061398853 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295059594897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_27 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (83142617777573 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (45901271533 / 2000000000000 : ℝ))
      (E := (cell12365 ⟨27, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (83142617777573 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (45901271533 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_28 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (83108198347769 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147533772477 / 50000000000000 : ℝ))
      (E := (cell12365 ⟨28, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (83108198347769 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147533772477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_29 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (10384225384659 / 12500000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (573767890291 / 25000000000000 : ℝ))
      (E := (cell12365 ⟨29, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (10384225384659 / 12500000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (573767890291 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_30 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (3321577277363 / 4000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147537784769 / 50000000000000 : ℝ))
      (E := (cell12365 ⟨30, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (3321577277363 / 4000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147537784769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_31 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (41502542443169 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (229507957251 / 10000000000000 : ℝ))
      (E := (cell12365 ⟨31, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (41502542443169 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (229507957251 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_32 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (4148538095119 / 5000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295083572289 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨32, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (4148538095119 / 5000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295083572289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_33 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (41468231475343 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147543756149 / 50000000000000 : ℝ))
      (E := (cell12365 ⟨33, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (41468231475343 / 50000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147543756149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_34 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (82902187999899 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (7172160973 / 312500000000 : ℝ))
      (E := (cell12365 ⟨34, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (82902187999899 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (7172160973 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_35 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (82867937018823 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295095512467 / 100000000000000 : ℝ))
      (E := (cell12365 ⟨35, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (82867937018823 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (2295095512467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_36 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (82833709976419 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (459019903383 / 20000000000000 : ℝ))
      (E := (cell12365 ⟨36, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (82833709976419 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (459019903383 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_37 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (8279950684181 / 10000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147551762883 / 50000000000000 : ℝ))
      (E := (cell12365 ⟨37, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (8279950684181 / 10000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147551762883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_38 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (82765327584271 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (459021507973 / 20000000000000 : ℝ))
      (E := (cell12365 ⟨38, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (82765327584271 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (459021507973 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12365_39 : CellCertificate 12365 (448146426008867 / 5000000000000000 : ℝ) (424678847693919 / 250000000000000000 : ℝ) (85840167672811 / 2500000000000000 : ℝ)
    (cell12365 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · norm_num [cell12365]
  · have h := gap_lower (n := 12365) (a := (82731172173237 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147555750569 / 50000000000000 : ℝ))
      (E := (cell12365 ⟨39, by decide⟩).energy) (xi := (85840167672811 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12365 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12365]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12365])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12365) (a := (82731172173237 / 100000000000000 : ℝ)) (b := (166639599803 / 100000000000000 : ℝ)) (q := (1147555750569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12365])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12365]

theorem cert12366_20 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (41692111796189 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (286862129987 / 12500000000000 : ℝ))
      (E := (cell12366 ⟨20, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (41692111796189 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (286862129987 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_21 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (3333985378463 / 4000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147450510093 / 50000000000000 : ℝ))
      (E := (cell12366 ⟨21, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (3333985378463 / 4000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147450510093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_22 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (41657534859169 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294905023621 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨22, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (41657534859169 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294905023621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_23 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (16656105865897 / 20000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294908996269 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨23, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (16656105865897 / 20000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294908996269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_24 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (83246013262007 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147456500273 / 50000000000000 : ℝ))
      (E := (cell12366 ⟨24, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (83246013262007 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147456500273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_25 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (41605760741533 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147458520179 / 50000000000000 : ℝ))
      (E := (cell12366 ⟨25, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (41605760741533 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147458520179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_26 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (83177053959991 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294921002607 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨26, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (83177053959991 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294921002607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_27 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (83142610660281 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294925007407 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨27, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (83142610660281 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294925007407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_28 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (41554095775799 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294928999529 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨28, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (41554095775799 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294928999529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_29 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (3322951864071 / 4000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294932981869 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨29, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (3322951864071 / 4000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294932981869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_30 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (41519712889403 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (91797480623 / 4000000000000 : ℝ))
      (E := (cell12366 ⟨30, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (41519712889403 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (91797480623 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_31 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (83005079050851 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147470493073 / 50000000000000 : ℝ))
      (E := (cell12366 ⟨31, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (83005079050851 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147470493073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_32 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (82970756386231 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294945012769 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨32, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (82970756386231 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294945012769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_33 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (82936457753431 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294948980387 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨33, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (82936457753431 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294948980387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_34 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (41451091560547 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147476503913 / 50000000000000 : ℝ))
      (E := (cell12366 ⟨34, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (41451091560547 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147476503913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_35 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (41433966229013 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147478489739 / 50000000000000 : ℝ))
      (E := (cell12366 ⟨35, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (41433966229013 / 50000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147478489739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_36 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (8283370573319 / 10000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147480477593 / 50000000000000 : ℝ))
      (E := (cell12366 ⟨36, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (8283370573319 / 10000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (1147480477593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_37 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (82799502915707 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294964994659 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨37, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (82799502915707 / 100000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294964994659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_38 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (10345665496857 / 12500000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294968981473 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨38, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (10345665496857 / 12500000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294968981473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12366_39 : CellCertificate 12366 (896263444010941 / 10000000000000000 : ℝ) (1698577974554189 / 1000000000000000000 : ℝ) (171666089983319 / 5000000000000000 : ℝ)
    (cell12366 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · norm_num [cell12366]
  · have h := gap_lower (n := 12366) (a := (8273116888007 / 10000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294972974867 / 100000000000000 : ℝ))
      (E := (cell12366 ⟨39, by decide⟩).energy) (xi := (171666089983319 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12366 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12366]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12366])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12366) (a := (8273116888007 / 10000000000000 : ℝ)) (b := (166625948439 / 100000000000000 : ℝ)) (q := (2294972974867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12366])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12366]

theorem cert12367_20 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (83384214216401 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (11473792771 / 500000000000 : ℝ))
      (E := (cell12367 ⟨20, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (83384214216401 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (11473792771 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_21 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (16669925081967 / 20000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (286845319129 / 12500000000000 : ℝ))
      (E := (cell12367 ⟨21, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (16669925081967 / 20000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (286845319129 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_22 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (4165753049519 / 5000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294766517493 / 100000000000000 : ℝ))
      (E := (cell12367 ⟨22, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (4165753049519 / 5000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294766517493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_23 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (41640260462429 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (229477051021 / 10000000000000 : ℝ))
      (E := (cell12367 ⟨23, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (41640260462429 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (229477051021 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_24 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (83246005180259 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (71711704229 / 3125000000000 : ℝ))
      (E := (cell12367 ⟨24, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (83246005180259 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (71711704229 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_25 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (83211513723747 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294778538393 / 100000000000000 : ℝ))
      (E := (cell12367 ⟨25, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (83211513723747 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294778538393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_26 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (1663540930453 / 2000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294782523007 / 100000000000000 : ℝ))
      (E := (cell12367 ⟨26, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (1663540930453 / 2000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294782523007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_27 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (83142603544469 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294786492533 / 100000000000000 : ℝ))
      (E := (cell12367 ⟨27, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (83142603544469 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294786492533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_28 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (20777046189217 / 25000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (286848813567 / 12500000000000 : ℝ))
      (E := (cell12367 ⟨28, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (20777046189217 / 25000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (286848813567 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_29 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (41536895063839 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (229479451553 / 10000000000000 : ℝ))
      (E := (cell12367 ⟨29, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (41536895063839 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (229479451553 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_30 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (83039419624897 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294798516177 / 100000000000000 : ℝ))
      (E := (cell12367 ⟨30, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (83039419624897 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294798516177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_31 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (20751268304171 / 25000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294802512913 / 100000000000000 : ℝ))
      (E := (cell12367 ⟨31, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (20751268304171 / 25000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294802512913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_32 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (41485375435681 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294806507941 / 100000000000000 : ℝ))
      (E := (cell12367 ⟨32, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (41485375435681 / 50000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294806507941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_33 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (10367056569677 / 12500000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147405251617 / 50000000000000 : ℝ))
      (E := (cell12367 ⟨33, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (10367056569677 / 12500000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147405251617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_34 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (82902178243491 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294814500539 / 100000000000000 : ℝ))
      (E := (cell12367 ⟨34, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (82902178243491 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (2294814500539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_35 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (10358490987299 / 12500000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (573704625343 / 25000000000000 : ℝ))
      (E := (cell12367 ⟨35, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (10358490987299 / 12500000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (573704625343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_36 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (82833701491083 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147411253513 / 50000000000000 : ℝ))
      (E := (cell12367 ⟨36, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (82833701491083 / 100000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147411253513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_37 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (2587484343459 / 3125000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (28685330749 / 1250000000000 : ℝ))
      (E := (cell12367 ⟨37, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (2587484343459 / 3125000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (28685330749 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_38 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (20691330091621 / 25000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147415239079 / 50000000000000 : ℝ))
      (E := (cell12367 ⟨38, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (20691330091621 / 25000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (1147415239079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12367_39 : CellCertificate 12367 (896234040582687 / 10000000000000000 : ℝ) (424610145140813 / 250000000000000000 : ℝ) (343303694074321 / 10000000000000000 : ℝ)
    (cell12367 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · norm_num [cell12367]
  · have h := gap_lower (n := 12367) (a := (20682791396977 / 25000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (286854312967 / 12500000000000 : ℝ))
      (E := (cell12367 ⟨39, by decide⟩).energy) (xi := (343303694074321 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12367 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12367]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12367])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12367) (a := (20682791396977 / 25000000000000 : ℝ)) (b := (166612299337 / 100000000000000 : ℝ)) (q := (286854312967 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12367])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12367]

theorem cert12368_20 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (41692102421093 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294620122421 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨20, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (41692102421093 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294620122421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_21 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (10418702044977 / 12500000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (114731206993 / 5000000000000 : ℝ))
      (E := (cell12368 ⟨21, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (10418702044977 / 12500000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (114731206993 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_22 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (10414381533013 / 12500000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294628123703 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨22, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (10414381533013 / 12500000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294628123703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_23 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (5205032032617 / 6250000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294632136577 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨23, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (5205032032617 / 6250000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294632136577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_24 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (5202874818757 / 6250000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294636124287 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨24, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (5202874818757 / 6250000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294636124287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_25 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (83211505965987 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294640090671 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨25, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (83211505965987 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294640090671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_26 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (83177039086829 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294644097713 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨26, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (83177039086829 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294644097713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_27 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (83142596430137 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294648090439 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨27, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (83142596430137 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294648090439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_28 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (83108177963577 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294652071981 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨28, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (83108177963577 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294652071981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_29 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (41536891827491 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (229465610369 / 10000000000000 : ℝ))
      (E := (cell12368 ⟨29, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (41536891827491 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (229465610369 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_30 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (83039413472349 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294660071343 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨30, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (83039413472349 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294660071343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_31 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (41502533691919 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (573666023577 / 25000000000000 : ℝ))
      (E := (cell12368 ⟨31, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (41502533691919 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (573666023577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_32 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (41485372678887 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147334028903 / 50000000000000 : ℝ))
      (E := (cell12368 ⟨32, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (41485372678887 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147334028903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_33 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (41468223681321 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294672080839 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨33, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (41468223681321 / 50000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294672080839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_34 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (5181385835443 / 6250000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (91787041923 / 4000000000000 : ℝ))
      (E := (cell12368 ⟨34, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (5181385835443 / 6250000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (91787041923 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_35 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (82867923339919 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147340039077 / 50000000000000 : ℝ))
      (E := (cell12368 ⟨35, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (82867923339919 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147340039077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_36 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (82833697250099 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (573671013799 / 25000000000000 : ℝ))
      (E := (cell12368 ⟨36, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (82833697250099 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (573671013799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_37 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (82799495066751 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294688038839 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨37, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (82799495066751 / 100000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294688038839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_38 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (16553063351831 / 20000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294692088589 / 100000000000000 : ℝ))
      (E := (cell12368 ⟨38, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (16553063351831 / 20000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (2294692088589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12368_39 : CellCertificate 12368 (17924092834637 / 200000000000000 : ℝ) (1698303208797471 / 1000000000000000000 : ℝ) (343275213012917 / 10000000000000000 : ℝ)
    (cell12368 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · norm_num [cell12368]
  · have h := gap_lower (n := 12368) (a := (20682790574187 / 25000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147348014529 / 50000000000000 : ℝ))
      (E := (cell12368 ⟨39, by decide⟩).energy) (xi := (343275213012917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12368 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12368]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12368])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12368) (a := (20682790574187 / 25000000000000 : ℝ)) (b := (10412415781 / 6250000000000 : ℝ)) (q := (1147348014529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12368])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12368]

theorem cert12369_20 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (20846048867433 / 25000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147240872281 / 50000000000000 : ℝ))
      (E := (cell12369 ⟨20, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (20846048867433 / 25000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147240872281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_21 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (41674803655759 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294485780671 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨21, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (41674803655759 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294485780671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_22 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (20828760884877 / 25000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147244891981 / 50000000000000 : ℝ))
      (E := (cell12369 ⟨22, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (20828760884877 / 25000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147244891981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_23 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (41640252060263 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147246879371 / 50000000000000 : ℝ))
      (E := (cell12369 ⟨23, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (41640252060263 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147246879371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_24 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (16649197804313 / 20000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (91779910697 / 4000000000000 : ℝ))
      (E := (cell12369 ⟨24, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (16649197804313 / 20000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (91779910697 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_25 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (20802874552447 / 25000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294501755553 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨25, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (20802874552447 / 25000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294501755553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_26 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (5198564478283 / 6250000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147252863363 / 50000000000000 : ℝ))
      (E := (cell12369 ⟨26, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (5198564478283 / 6250000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147252863363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_27 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (16628517863457 / 20000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294509742717 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨27, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (16628517863457 / 20000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294509742717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_28 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (41554085585863 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147256874147 / 50000000000000 : ℝ))
      (E := (cell12369 ⟨28, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (41554085585863 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147256874147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_29 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (41536888591843 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (45890354927 / 2000000000000 : ℝ))
      (E := (cell12369 ⟨29, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (41536888591843 / 50000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (45890354927 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_30 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (2075985183029 / 2500000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147260869777 / 50000000000000 : ℝ))
      (E := (cell12369 ⟨30, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (2075985183029 / 2500000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147260869777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_31 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (10375632694039 / 12500000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294525730333 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨31, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (10375632694039 / 12500000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294525730333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_32 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (82970739845467 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294529720891 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨32, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (82970739845467 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294529720891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_33 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (82936442169109 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294533713201 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨33, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (82936442169109 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294533713201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_34 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (82902168491887 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147268854503 / 50000000000000 : ℝ))
      (E := (cell12369 ⟨34, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (82902168491887 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147268854503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_35 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (82867918782607 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147270854911 / 50000000000000 : ℝ))
      (E := (cell12369 ⟨35, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (82867918782607 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147270854911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_36 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (16566738602047 / 20000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147272858469 / 50000000000000 : ℝ))
      (E := (cell12369 ⟨36, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (16566738602047 / 20000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (1147272858469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_37 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (10349936392987 / 12500000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294549731417 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨37, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (10349936392987 / 12500000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294549731417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_38 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (82765313152869 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294553695431 / 100000000000000 : ℝ))
      (E := (cell12369 ⟨38, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (82765313152869 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (2294553695431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12369_39 : CellCertificate 12369 (896175247457313 / 10000000000000000 : ℝ) (1698165859251453 / 1000000000000000000 : ℝ) (343246736781047 / 10000000000000000 : ℝ)
    (cell12369 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · norm_num [cell12369]
  · have h := gap_lower (n := 12369) (a := (82731159006593 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (286819715863 / 12500000000000 : ℝ))
      (E := (cell12369 ⟨39, by decide⟩).energy) (xi := (343246736781047 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12369 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12369]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12369])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12369) (a := (82731159006593 / 100000000000000 : ℝ)) (b := (41646251979 / 25000000000000 : ℝ)) (q := (286819715863 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12369])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12369]

theorem cert12370_20 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (83384186099039 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147171739433 / 50000000000000 : ℝ))
      (E := (cell12370 ⟨20, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (83384186099039 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147171739433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_21 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (4167479913247 / 5000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294347475469 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨21, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (4167479913247 / 5000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294347475469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_22 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (83315034816593 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294351439979 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨22, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (83315034816593 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294351439979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_23 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (4164024786041 / 5000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294355435023 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨23, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (4164024786041 / 5000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294355435023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_24 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (83245980944617 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147179732371 / 50000000000000 : ℝ))
      (E := (cell12370 ⟨24, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (83245980944617 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147179732371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_25 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (20802872613787 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294363474679 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨25, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (20802872613787 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294363474679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_26 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (41588512109873 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147183734217 / 50000000000000 : ℝ))
      (E := (cell12370 ⟨26, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (41588512109873 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147183734217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_27 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (10392822775739 / 12500000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294371449369 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨27, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (10392822775739 / 12500000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294371449369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_28 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (16621632876263 / 20000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (573593855153 / 25000000000000 : ℝ))
      (E := (cell12370 ⟨28, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (16621632876263 / 20000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (573593855153 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_29 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (20768442678447 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (458875888703 / 20000000000000 : ℝ))
      (E := (cell12370 ⟨29, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (20768442678447 / 25000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (458875888703 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_30 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (83039401171331 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (573595850963 / 25000000000000 : ℝ))
      (E := (cell12370 ⟨30, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (83039401171331 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (573595850963 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_31 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (41502527861053 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (229438742099 / 10000000000000 : ℝ))
      (E := (cell12370 ⟨31, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (41502527861053 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (229438742099 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_32 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (41485367167219 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147195719337 / 50000000000000 : ℝ))
      (E := (cell12370 ⟨32, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (41485367167219 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (1147195719337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_33 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (5183527311051 / 6250000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (573598850081 / 25000000000000 : ℝ))
      (E := (cell12370 ⟨33, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (5183527311051 / 6250000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (573598850081 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_34 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (16580432723577 / 20000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294399424763 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨34, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (16580432723577 / 20000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294399424763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_35 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (10358489278307 / 12500000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294403396379 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨35, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (10358489278307 / 12500000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294403396379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_36 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (82833688771493 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294407433633 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨36, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (82833688771493 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294407433633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_37 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (82799487222123 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (143400713773 / 6250000000000 : ℝ))
      (E := (cell12370 ⟨37, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (82799487222123 / 100000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (143400713773 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_38 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (41382654773813 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294415416021 / 100000000000000 : ℝ))
      (E := (cell12370 ⟨38, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (41382654773813 / 50000000000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (2294415416021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12370_39 : CellCertificate 12370 (448072928878977 / 5000000000000000 : ℝ) (1698028531919809 / 1000000000000000000 : ℝ) (171609132688667 / 5000000000000000 : ℝ)
    (cell12370 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · norm_num [cell12370]
  · have h := gap_lower (n := 12370) (a := (258534861617 / 312500000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (573604855301 / 25000000000000 : ℝ))
      (E := (cell12370 ⟨39, by decide⟩).energy) (xi := (171609132688667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12370 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12370]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12370])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12370) (a := (258534861617 / 312500000000 : ℝ)) (b := (41642841399 / 25000000000000 : ℝ)) (q := (573604855301 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12370])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12370]

theorem cert12371_20 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (83384176730107 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294205267091 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨20, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (83384176730107 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294205267091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_21 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (83349589220083 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294209224251 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨21, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (83349589220083 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294209224251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_22 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (83315026095357 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147106604169 / 50000000000000 : ℝ))
      (E := (cell12371 ⟨22, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (83315026095357 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147106604169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_23 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (41640243661377 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294217223733 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨23, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (41640243661377 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294217223733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_24 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (83245972869269 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294221216239 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨24, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (83245972869269 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294221216239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_25 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (83211482702067 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294225248051 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨25, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (83211482702067 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294225248051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_26 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (83177016788483 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294229206067 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨26, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (83177016788483 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294229206067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_27 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (41571287548009 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (458846642079 / 20000000000000 : ℝ))
      (E := (cell12371 ⟨27, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (41571287548009 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (458846642079 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_28 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (41554078796171 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294237205803 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨28, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (41554078796171 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294237205803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_29 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (8307376424529 / 10000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294241195183 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨29, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (8307376424529 / 10000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294241195183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_30 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (83039395022861 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147122590599 / 50000000000000 : ℝ))
      (E := (cell12371 ⟨30, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (83039395022861 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147122590599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_31 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (83005049893219 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147124612391 / 50000000000000 : ℝ))
      (E := (cell12371 ⟨31, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (83005049893219 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147124612391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_32 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (8297072882469 / 10000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (143390825697 / 6250000000000 : ℝ))
      (E := (cell12371 ⟨32, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (8297072882469 / 10000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (143390825697 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_33 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (41468215892881 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294257200759 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨33, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (41468215892881 / 50000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294257200759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_34 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (20725539686271 / 25000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (143391324709 / 6250000000000 : ℝ))
      (E := (cell12371 ⟨34, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (20725539686271 / 25000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (143391324709 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_35 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (16573581934293 / 20000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147132598211 / 50000000000000 : ℝ))
      (E := (cell12371 ⟨35, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (16573581934293 / 20000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (1147132598211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_36 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (5177105283367 / 6250000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294269205281 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨36, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (5177105283367 / 6250000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294269205281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_37 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (82799483301431 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294273164337 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨37, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (82799483301431 / 100000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294273164337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_38 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (646603952683 / 781250000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294277191693 / 100000000000000 : ℝ))
      (E := (cell12371 ⟨38, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (646603952683 / 781250000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (2294277191693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12371_39 : CellCertificate 12371 (56007279539541 / 625000000000000 : ℝ) (424472806699287 / 250000000000000000 : ℝ) (343189798800403 / 10000000000000000 : ℝ)
    (cell12371 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · norm_num [cell12371]
  · have h := gap_lower (n := 12371) (a := (8273115242929 / 10000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (45885623413 / 2000000000000 : ℝ))
      (E := (cell12371 ⟨39, by decide⟩).energy) (xi := (343189798800403 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12371 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12371]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12371])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12371) (a := (8273115242929 / 10000000000000 : ℝ)) (b := (5204928923 / 3125000000000 : ℝ)) (q := (45885623413 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12371])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12371]

theorem cert12372_20 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (16676833472587 / 20000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (458813410199 / 20000000000000 : ℝ))
      (E := (cell12372 ⟨20, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (16676833472587 / 20000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (458813410199 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_21 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (16669916035389 / 20000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294071085289 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨21, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (16669916035389 / 20000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294071085289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_22 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (83315017375801 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147037544521 / 50000000000000 : ℝ))
      (E := (cell12372 ⟨22, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (83315017375801 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147037544521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_23 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (83280478926327 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147039533281 / 50000000000000 : ℝ))
      (E := (cell12372 ⟨23, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (83280478926327 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147039533281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_24 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (83245964795519 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147041540129 / 50000000000000 : ℝ))
      (E := (cell12372 ⟨24, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (83245964795519 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147041540129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_25 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (16642294990109 / 20000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (229408707567 / 10000000000000 : ℝ))
      (E := (cell12372 ⟨25, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (16642294990109 / 20000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (229408707567 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_26 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (41588504679369 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294091056397 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨26, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (41588504679369 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294091056397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_27 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (41571283993801 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294095025799 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨27, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (41571283993801 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294095025799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_28 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (10388518850601 / 12500000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147049522717 / 50000000000000 : ℝ))
      (E := (cell12372 ⟨28, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (10388518850601 / 12500000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147049522717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_29 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (8307375777819 / 10000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (573525764953 / 25000000000000 : ℝ))
      (E := (cell12372 ⟨29, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (8307375777819 / 10000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (573525764953 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_30 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (83039388875749 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147053506557 / 50000000000000 : ℝ))
      (E := (cell12372 ⟨30, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (83039388875749 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147053506557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_31 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (1660100881313 / 2000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147055512353 / 50000000000000 : ℝ))
      (E := (cell12372 ⟨31, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (1660100881313 / 2000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147055512353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_32 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (4148536165811 / 5000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (229411503833 / 10000000000000 : ℝ))
      (E := (cell12372 ⟨32, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (4148536165811 / 5000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (229411503833 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_33 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (20734106648987 / 25000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (573529763989 / 25000000000000 : ℝ))
      (E := (cell12372 ⟨33, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (20734106648987 / 25000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (573529763989 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_34 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (82902153873483 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (143382688797 / 6250000000000 : ℝ))
      (E := (cell12372 ⟨34, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (82902153873483 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (143382688797 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_35 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (16573581023527 / 20000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (573531762839 / 25000000000000 : ℝ))
      (E := (cell12372 ⟨35, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (16573581023527 / 20000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (573531762839 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_36 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (20708420074343 / 25000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (573532757971 / 25000000000000 : ℝ))
      (E := (cell12372 ⟨36, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (20708420074343 / 25000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (573532757971 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_37 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (82799479381821 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294135021969 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨37, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (82799479381821 / 100000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294135021969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_38 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (10345662792533 / 12500000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294139022449 / 100000000000000 : ℝ))
      (E := (cell12372 ⟨38, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (10345662792533 / 12500000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (2294139022449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12372_39 : CellCertificate 12372 (8960870920803 / 100000000000000 : ℝ) (424438485969521 / 250000000000000000 : ℝ) (343161337048877 / 10000000000000000 : ℝ)
    (cell12372 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · norm_num [cell12372]
  · have h := gap_lower (n := 12372) (a := (41365574571071 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147071516967 / 50000000000000 : ℝ))
      (E := (cell12372 ⟨39, by decide⟩).energy) (xi := (343161337048877 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12372 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12372]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12372])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12372) (a := (41365574571071 / 50000000000000 : ℝ)) (b := (33308817547 / 20000000000000 : ℝ)) (q := (1147071516967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12372])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12372]

theorem cert12373_20 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (83384157997523 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293929005311 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨20, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (83384157997523 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293929005311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_21 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (83349571135527 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (573483250079 / 25000000000000 : ℝ))
      (E := (cell12373 ⟨21, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (83349571135527 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (573483250079 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_22 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (83315008657923 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (573484241377 / 25000000000000 : ℝ))
      (E := (cell12373 ⟨22, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (83315008657923 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (573484241377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_23 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (41640235265769 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293940963509 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨23, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (41640235265769 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293940963509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_24 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (10405744590421 / 12500000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (57348623503 / 2500000000000 : ℝ))
      (E := (cell12373 ⟨24, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (10405744590421 / 12500000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (57348623503 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_25 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (83211467200581 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293948957537 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨25, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (83211467200581 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293948957537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_26 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (5198562620657 / 6250000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293952961039 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨26, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (5198562620657 / 6250000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293952961039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_27 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (16628512176133 / 20000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293956953987 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨27, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (16628512176133 / 20000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293956953987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_28 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (10388518002339 / 12500000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1146980469753 / 50000000000000 : ℝ))
      (E := (cell12373 ⟨28, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (10388518002339 / 12500000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1146980469753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_29 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (10384218914061 / 12500000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293964920491 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨29, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (10384218914061 / 12500000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293964920491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_30 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (20759845682499 / 25000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (3584326497 / 156250000000 : ℝ))
      (E := (cell12373 ⟨30, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (20759845682499 / 25000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (3584326497 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_31 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (83005038239401 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1146986468883 / 50000000000000 : ℝ))
      (E := (cell12373 ⟨31, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (83005038239401 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1146986468883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_32 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (8297071780903 / 10000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (458795384041 / 20000000000000 : ℝ))
      (E := (cell12373 ⟨32, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (8297071780903 / 10000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (458795384041 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_33 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (82936421407373 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1146990453683 / 50000000000000 : ℝ))
      (E := (cell12373 ⟨33, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (82936421407373 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1146990453683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_34 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (82902149003081 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (573496225247 / 25000000000000 : ℝ))
      (E := (cell12373 ⟨34, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (82902149003081 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (573496225247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_35 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (20716975141241 / 25000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1146994451293 / 50000000000000 : ℝ))
      (E := (cell12373 ⟨35, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (20716975141241 / 25000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1146994451293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_36 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (10354209507749 / 12500000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293992913443 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨36, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (10354209507749 / 12500000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293992913443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_37 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (82799475463291 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293996934621 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨37, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (82799475463291 / 100000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2293996934621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_38 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (41382649369073 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2294000908287 / 100000000000000 : ℝ))
      (E := (cell12373 ⟨38, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (41382649369073 / 50000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (2294000908287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12373_39 : CellCertificate 12373 (112007214512471 / 1250000000000000 : ℝ) (106101042697327 / 62500000000000000 : ℝ) (343132880121383 / 10000000000000000 : ℝ)
    (cell12373 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · norm_num [cell12373]
  · have h := gap_lower (n := 12373) (a := (20682786463999 / 25000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147002446837 / 50000000000000 : ℝ))
      (E := (cell12373 ⟨39, by decide⟩).energy) (xi := (343132880121383 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12373 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12373]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12373])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12373) (a := (20682786463999 / 25000000000000 : ℝ)) (b := (166530452193 / 100000000000000 : ℝ)) (q := (1147002446837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12373])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12373]

theorem cert12374_20 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (8338414863387 / 10000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293790955309 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨20, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (8338414863387 / 10000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293790955309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_21 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (83349562095827 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146897455533 / 50000000000000 : ℝ))
      (E := (cell12374 ⟨21, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (83349562095827 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146897455533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_22 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (20828749985431 / 25000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293798954321 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨22, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (20828749985431 / 25000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293798954321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_23 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (20820115534597 / 25000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (143362682161 / 6250000000000 : ℝ))
      (E := (cell12374 ⟨23, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (20820115534597 / 25000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (143362682161 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_24 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (16649189730563 / 20000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (573451728127 / 25000000000000 : ℝ))
      (E := (cell12374 ⟨24, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (16649189730563 / 20000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (573451728127 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_25 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (41605729726087 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (458762178731 / 20000000000000 : ℝ))
      (E := (cell12374 ⟨25, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (41605729726087 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (458762178731 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_26 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (83176994503803 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (573453729999 / 25000000000000 : ℝ))
      (E := (cell12374 ⟨26, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (83176994503803 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (573453729999 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_27 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (16628510755041 / 20000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (573454734139 / 25000000000000 : ℝ))
      (E := (cell12374 ⟨27, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (16628510755041 / 20000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (573454734139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_28 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (83108137234053 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (286727861003 / 12500000000000 : ℝ))
      (E := (cell12374 ⟨28, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (83108137234053 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (286727861003 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_29 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (10384218106023 / 12500000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (286728361767 / 12500000000000 : ℝ))
      (E := (cell12374 ⟨29, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (10384218106023 / 12500000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (286728361767 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_30 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (83039376585601 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (114691544957 / 5000000000000 : ℝ))
      (E := (cell12374 ⟨30, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (83039376585601 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (114691544957 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_31 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (83005032414469 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146917452733 / 50000000000000 : ℝ))
      (E := (cell12374 ⟨31, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (83005032414469 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146917452733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_32 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (82970712303117 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293838915311 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨32, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (82970712303117 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293838915311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_33 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (20734104055009 / 25000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293842872093 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨33, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (20734104055009 / 25000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293842872093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_34 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (41451072066939 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293846894629 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨34, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (41451072066939 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293846894629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_35 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (82867896013453 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146925433653 / 50000000000000 : ℝ))
      (E := (cell12374 ⟨35, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (82867896013453 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (1146925433653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_36 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (20708417956933 / 25000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293854908581 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨36, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (20708417956933 / 25000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293854908581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_37 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (41399735772921 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (458771780459 / 20000000000000 : ℝ))
      (E := (cell12374 ⟨37, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (41399735772921 / 50000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (458771780459 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_38 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (82765295137069 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293862849213 / 100000000000000 : ℝ))
      (E := (cell12374 ⟨38, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (82765295137069 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (2293862849213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

theorem cert12374_39 : CellCertificate 12374 (448014172344971 / 5000000000000000 : ℝ) (1697479444629207 / 1000000000000000000 : ℝ) (171552214008273 / 5000000000000000 : ℝ)
    (cell12374 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · norm_num [cell12374]
  · have h := gap_lower (n := 12374) (a := (82731142570853 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (458773373451 / 20000000000000 : ℝ))
      (E := (cell12374 ⟨39, by decide⟩).energy) (xi := (171552214008273 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12374 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12374]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12374])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12374) (a := (82731142570853 / 100000000000000 : ℝ)) (b := (41629204727 / 25000000000000 : ℝ)) (q := (458773373451 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12374])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12374]

end BstLean.Part268
